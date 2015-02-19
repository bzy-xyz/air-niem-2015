#!/usr/bin/python

import os
import sys
import cgi
import traceback
import StringIO
import urllib
import re

import time

import rdflib
import merge
import tempfile

from multiprocessing import Process, Queue

#from cwmrete.tmswap import policyrunner
#from cwmrete.tmswap import llyn
#from cwmrete.tmswap.RDFSink import SUBJ, PRED, OBJ
#from cwmrete.tmswap import uripath

import render_law_multiple

import logging
logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)

from memory_profiler import memory_usage

_filter_properties = [
    'http://dig.csail.mit.edu/TAMI/2007/amord/air#compliant-with',
    'http://dig.csail.mit.edu/TAMI/2007/amord/air#non-compliant-with']

_log_boilerplate = """
@prefix : <http://dig.csail.mit.edu/2010/DHS-fusion/common/fusion_ONT#>.
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.
"""

_transaction_uri = ("http://dig.csail.mit.edu/2010/DHS-fusion/common/"
                    "fusion_ONT#Transaction")

_subjective_form_boilerplate = """
<html>
<head>
    <link type="text/css" href="css/custom.css" rel="stylesheet" />
</head>
<body>

<table>
    <tr>
        <td>Transaction sender:</td>
        <td>%s</td>
    </tr>
    <tr>
        <td>Transaction receiver:</td>
        <td>%s</td>
    </tr>
    <tr>
        <td>Transaction file:</td>
        <td>%s</td>
    </tr>
<table>

<form name="subjective_questions" action="dhs_air_integrated.py" method="get">

<input type="hidden" name="subjectives" value="true" />

%s

<br/>
<table>
%s
</table>

<br/>
<input type="submit" value="Submit" />
</form>
</body>
</html>
"""

_xmp_parser = "http://dice.csail.mit.edu/xmpparser.py"

_store = None

_rdfs_prefix = "http://www.w3.org/2000/01/rdf-schema"
_air_prefix = "http://dig.csail.mit.edu/TAMI/2007/amord/air"
_fusion_prefix = "http://dig.csail.mit.edu/2010/DHS-fusion/common/fusion_ONT"

_see_also_predicate = "%s#seeAlso" % _rdfs_prefix
_label_predicate = "%s#label" % _rdfs_prefix

_to_predicate = "%s#to" % _fusion_prefix
_to_subj = "%s#Event" % _fusion_prefix
_rule_predicate = "%s#based_upon" % _fusion_prefix
_data_predicate = "%s#data" % _fusion_prefix

_transaction_predicate = "%s#transaction_ontology" % _fusion_prefix

_air_description = "%s#description" % _air_prefix
_air_statement = "%s#statement" % _air_prefix

_subjective_object = "%s#Subjective" % _air_prefix
_subjective_term_predicate = "%s#subjective_term" % _air_prefix
_subjective_term_sender = "%s#Sender" % _air_prefix
_subjective_term_receiver = "%s#Receiver" % _air_prefix
_subjective_term_data = "%s#Data" % _air_prefix
_subjective_term_transaction = "%s#Transaction" % _air_prefix

# fast stable uniqueify
def uniqueify(seq):
    seen = {}
    result = []
    for item in seq:
        if item in seen:
            continue
        seen[item] = 1
        result.append(item)
    return result

def url_to_context(url):
    context = _store.load(uripath.splitFrag(url)[0],
                          remember = 0, referer = '', topLevel = True)
    context.reopen()
    context.stayOpen = 1
    return context

def get_subjective_terms(context):
    term_dict = {}
    subjective_term_pred = context.newSymbol(_subjective_term_predicate)
    subjective_bindings = context.statementsMatching(pred=subjective_term_pred)
    for elem in subjective_bindings:
        term_dict[elem[SUBJ]] = elem[OBJ]
    return term_dict

def get_subjective_rules(context):
    rule_dict = {}
    subjective_object = context.newSymbol(_subjective_object)
    subjective_rules = context.statementsMatching(obj=subjective_object)
    air_description = context.newSymbol(_air_description)
    air_statement = context.newSymbol(_air_statement)
    for elem in subjective_rules:
        rule_name = elem[SUBJ]
        descr = context.the(subj = rule_name, pred = air_description)
        triple = context.the(subj = rule_name, pred = air_statement)
        rule_dict[rule_name] = (descr, triple)
    return rule_dict

def render_subjective_form(term_dict, rule_dict, name_dict):
    output = []
    template = """
    <tr>
        <td><input type="checkbox" name="subjective" value="%s"/></td>
        <td>%s</td>
    </tr>"""
    for rule in sorted(rule_dict.keys()):
        tokens = []
        for token in rule_dict[rule][0]:
            if token in term_dict:
                assert term_dict[token] in name_dict
                tokens.append(name_dict[term_dict[token]])
            else:
                tokens.append(str(token))
        output.append(template % (rule, ''.join(tokens)))
    return ''.join(output)

def evaluate_seealso(context):
    see_also_pred = context.newSymbol(_see_also_predicate)
    see_alsos = context.statementsMatching(pred=see_also_pred)
    return [str(elem[OBJ]) for elem in see_alsos]

def get_transaction_ontology(context):
    transaction_pred = context.newSymbol(_transaction_predicate)
    transaction = context.statementsMatching(pred=transaction_pred)
    if not transaction:
        return None
    return str(transaction[0][OBJ])

def foaf_to_canonical_name(context):
    label_pred = context.newSymbol(_label_predicate)
    foaf_label = context.statementsMatching(pred=label_pred)
    if not foaf_label:
        return url
    return str(foaf_label[0][OBJ])

def obtain_to_uris_list(context):
    logging.debug("_to_predicate is %s ", _to_predicate)
    logging.debug("context: %s", context)
    to_pred = context.newSymbol(_to_predicate)
    to_subj = context.newSymbol(_to_subj)

    to_list = context.statementsMatching(subj=to_subj)
    logging.debug("to_list: %s", to_list)
    to_uris_list = context.statementsMatching(pred=to_pred)
    logging.debug("to_uris is: %s ", to_uris_list)

    if not to_uris_list:
        return url

    uris_list = []
    for to_uris in to_uris_list:
        to_uri = to_uris[OBJ]
        uris_list.append(str(to_uri))

    return uris_list

def obtain_rule_uris_list(context):
    rule_pred = context.newSymbol(_rule_predicate)

    rule_uris_list = context.statementsMatching(pred=rule_pred)
    if not rule_uris_list:
        return url

    uris_list = []
    for rule_uris in rule_uris_list:
        rule_uri = rule_uris[OBJ]
        uris_list.append(str(rule_uri))

    logging.debug("rule uris_list: %s", uris_list)
    return uris_list

def obtain_data_uris_list(context):
    data_pred = context.newSymbol(_data_predicate)

    data_uris_list = context.statementsMatching(pred=data_pred)
    if not data_uris_list:
        return url

    uris_list = []
    for data_uris in data_uris_list:
        data_uri = data_uris[OBJ]
        uris_list.append(str(data_uri))

    logging.debug("data uris_list: %s", uris_list)
    return uris_list


def generate_log(by_uri, to_uri, data_uri, policy_uri,
                 by_label = None, to_label = None, data_label = None):

    logging.debug("data_uri: %s", data_uri)
    
    g = rdflib.Graph()
    g.bind("","http://dig.csail.mit.edu/2010/DHS-fusion/common/fusion_ONT#")
    
    trans = rdflib.URIRef(_transaction_uri)
    
    g.add((trans, rdflib.namespace.RDF.type, rdflib.URIRef("{0}#Request".format(policy_uri))))
    g.add((trans, rdflib.namespace.RDF.type, rdflib.URIRef("{0}#Disseminate".format(policy_uri))))
    
    g.add((trans, rdflib.URIRef("{0}#by".format(policy_uri)), rdflib.URIRef(by_uri)))
    g.add((trans, rdflib.URIRef("{0}#to".format(policy_uri)), rdflib.URIRef(to_uri)))
    g.add((trans, rdflib.URIRef("{0}#data".format(policy_uri)), rdflib.URIRef(data_uri)))

    g.add((rdflib.URIRef(by_uri), rdflib.URIRef(_label_predicate), rdflib.Literal(by_label)))
    g.add((rdflib.URIRef(to_uri), rdflib.URIRef(_label_predicate), rdflib.Literal(to_label)))
    g.add((rdflib.URIRef(data_uri), rdflib.URIRef(_label_predicate), rdflib.Literal(data_label)))
    
    g2, s = merge.merge([by_uri, to_uri, data_uri], ["http://link.csail.mit.edu/projects/prod/2015/air-niem-compatibility/xsd/niem/niem-core/3.0/niem-core.xsd"])
    
    stmp = tempfile.NamedTemporaryFile()
    gtmp = tempfile.NamedTemporaryFile()

    stmp.write(s.serialize(format='n3'))
    gtmp.write(g2.serialize(format='n3'))

    stmp.flush()
    gtmp.flush()
    
    g.parse(stmp.name, format='n3')
    g.parse(gtmp.name, format='n3')
    
    return g.serialize(format='n3')
    

def format_headers(content_type, content):
    output_buffer = []

    output_buffer.append("Content-type: %s\n" % content_type)
    output_buffer.append("Content-Length: %d\n" % len(content))
    output_buffer.append("\n")
    output_buffer.append(content)

    return ''.join(output_buffer)

def copy_params(form):
    hidden_template = '<input type="hidden" name="%s" value="%s" />\n'
    output_buffer = []
    for key in form.keys():
        for value in form.getlist(key):
            output_buffer.append(hidden_template % (key, value))
    return ''.join(output_buffer)

def get_subjective_html(form, subjective_zip, by_label,
                        to_label, data_label, transaction_label):
    elements = []
    for context, terms, rules in subjective_zip:
        sym_to_label = {
            context.newSymbol(_subjective_term_sender): by_label,
            context.newSymbol(_subjective_term_receiver): to_label,
            context.newSymbol(_subjective_term_data): data_label,
            context.newSymbol(_subjective_term_transaction): transaction_label,
            }
        elements.append(render_subjective_form(terms, rules, sym_to_label))
    return _subjective_form_boilerplate % (
        by_label, to_label, data_label, copy_params(form), ''.join(elements))

def get_subjective_log(subjective_zip, active_rule, by_uri, to_uri,
                       data_uri, transaction_uri):
    new_triples = []
    for context, terms, rules in subjective_zip:
        sym_mapping = {
            context.newSymbol(_subjective_term_sender): by_uri,
            context.newSymbol(_subjective_term_receiver): to_uri,
            context.newSymbol(_subjective_term_data): data_uri,
            context.newSymbol(_subjective_term_transaction): transaction_uri,
            }

        for rule in rules:
            if active_rule == str(rule):
                for triple in rules[rule][1]:
                    if triple[SUBJ] in terms:
                        subject = sym_mapping[terms[triple[SUBJ]]]
                    else:
                        subject = triple[SUBJ].uriref()

                    if triple[OBJ] in terms:
                        object = sym_mapping[terms[triple[OBJ]]]
                    else:
                        object = triple[OBJ].uriref()

                    new_triples.append("<%s> <%s> <%s>." % (
                        subject, triple[PRED].uriref(), object))
    return '\n'.join(new_triples)


def mem(size="rss"):
    """ Generalization: memory sizes: rss, rsz, vsz. """
    return int(os.popen('ps -p %d -o %s | tail -1' % (os.getpid(),size)).read())

def really_run_reasoner(q, form, by_uri, to_uri, data_uri, rules_contexts, see_also, log_uris, rule_uris, logs, rules):
    # The first time q.put() is called, it should be used to write out
    # the return value. It should be a pair (type-string,
    # response-content) OR (None, None) to collect values over
    # a number of runs.  The (type-string, response-content) content
    # will be returned by the parent caller as a CGI response.

    # Yet another function to make sure that policyrunner.testPolicy
    # runs in a separate process each time it is called.
    current_timings = {}
    current_memory_usage = {}

    if (by_uri and to_uri and data_uri):

        log_generated_time_start = time.time()
        log_generated_memory_start = mem("rss")

        by_context = url_to_context(by_uri)
        to_context = url_to_context(to_uri)

        see_also.extend(evaluate_seealso(by_context))
        see_also.extend(evaluate_seealso(to_context))

        if form.getfirst('by_label'):
            by_label = form.getfirst('by_label')
        else:
	    # TODO what we really want to do here is grab a proper name
            #by_label = foaf_to_canonical_name(by_context)
	    by_label = by_uri

        if form.getfirst('to_label'):
            to_label = form.getfirst('to_label')
        else:
            # to_label = foaf_to_canonical_name(to_context)
	    to_label = to_uri

        if form.getfirst('data_label'):
            data_label = form.getfirst('data_label')
        else:
            data_url = form.getfirst('data')
            rightmost_slash = data_url.rfind('/')
            if rightmost_slash != -1:
                data_label = data_url[rightmost_slash + 1:]
            else:
                data_label = data_url

        if form.getfirst('transaction_label'):
            transaction_label = form.getfirst('transaction_label')
        else:
            transaction_label = "Transaction"

        if form.getfirst('policy'):
            transaction_policy = form.getfirst('policy')
        else:
            transaction_policy = get_transaction_ontology(rules_contexts[0])

        log = generate_log(by_uri, to_uri, data_uri, transaction_policy,
                           by_label, to_label, data_label)

        log_generated_time_end = time.time()
        log_generated_memory_end = mem("rss")

        current_timings['log_generated_time'] = time.time()
        log_generated_time = log_generated_time_end
        log_generated_memory = log_generated_memory_end

        lgtval = log_generated_time_end - log_generated_time_start
        logging.debug("log generation time (atm): " + str(lgtval))
        current_memory_usage['log_generated_size'] = mem("rss")

        subjective_terms = [get_subjective_terms(i) for i in rules_contexts]
        subjective_rules = [get_subjective_rules(i) for i in rules_contexts]

        logging.debug("subjective_terms: %s, subjective_rules: %s", subjective_terms, subjective_rules)

        subjective_zip = zip(rules_contexts, subjective_terms, subjective_rules)

        if any(subjective_rules):
            logging.debug("if any(subjective_rules)")
            if form.getfirst("subjectives"):
                logging.debug("if form.getfirst")
                for active_rule in form.getlist("subjective"):
                    subjective_log = get_subjective_log(
                        subjective_zip, active_rule,
                        by_uri, to_uri, data_uri, _transaction_uri)
                    log = "%s\n%s" % (log, subjective_log)
                    logging.debug("for loop done, log: %s", log)
            else:
                html_output = get_subjective_html(
                    form, subjective_zip, by_label,
                    to_label, data_label, transaction_label)
                #return ('text/html', html_output)
                q.put(('text/html', html_output))
                return
    else:
        current_timings['log_generated_time'] = time.time()
        log_generated_time = time.time()

        current_memory_usage['log_generted_size'] = mem("rss")
    #### data uri if ends here ####
 
    if form.getfirst('print_preprocessing'):
        output_str = []
        output_str.append("rdfs:seeAlso urls found (%d):\n\t%s" % (
            len(see_also), '\n\t'.join(see_also)))
        output_str.append("rdfs:transaction uri used:\n\t%s" % (
            transaction_policy))
        output_str.append("Canonical by: %s\nCanonical to: %s" % (
            by_label, to_label))
        output_str.append("\nGenerated log:\n%s" % log)
        #return ('text/plain', '\n'.join(output_str))
        q.put(('text/plain', '\n'.join(output_str)))
        return
 
    #### print preprocessing if ends here ####

    logging.debug("print log: %s", form.getfirst('print_log'))

    if form.getfirst('print_log') == 'true':
        q.put(('text/plain', log))
        return
        #return ('text/plain', log)

    log_uris.extend(see_also)
    log_uris = uniqueify(log_uris)

    # HACK TO RESET STORE!
    RDFSink.runNamespaceValue = None
    policy_store = llyn.RDFStore()
    policyrunner.n3NS = policy_store.newSymbol('http://www.w3.org/2000/10/swap/grammar/n3#n3')
    # runPolicy()[0].n3String() instead of testPolicy() since
    # testPolicy binds the initial policyrunner.store to the store
    # argument (no good for resetting the store!)

    #logging.debug("rules_uri: %s, log: %s", rule_uris, log)

    currentMemoryStats = memory_usage(-1, interval=.2, timeout=1)
    #logging.debug("memory: %s", form.getfirst('memory'))
       
    #if form.getfirst('memory') == 'true':
    #    reasonerMemoryStats = memory_usage((policyrunner.testPolicy, (log_uris, rule_uris), {'logFormula': log, 'ruleFormula': rules, 'filterProperties': _filter_properties}))
    #    logging.debug("reasoner memroy stats: %s", reasonerMemoryStats)
    #    logging.debug("reasoner memory stats size: %s",
    #    len(reasonerMemoryStats))

    #    actualMemoryUsage = max(reasonerMemoryStats) - max(currentMemoryStats)
    #    header = 'text/plain'
    #    memory_usage_string = str(actualMemoryUsage) + 'MB'
    #    #q.put((header, memory_usage_string))
    #    #return
    #    #return (header, memory_usage_string)
    #else: 
    #    reasoner_str = policyrunner.testPolicy(
    #        log_uris, rule_uris, log, rules, _filter_properties).encode('utf-8')
 

    logging.debug("the log uris sent to the reasoner:")
    logging.debug(log_uris)
    logging.debug("the rule_uris sent to the reasoner:")
    logging.debug(rule_uris)
    logging.debug("the log sent to the reasoner:")
    logging.debug(log)
    logging.debug("the rules sent to the reasoner:")
    logging.debug(rules)

    reasoner_str = policyrunner.testPolicy(
        log_uris, rule_uris, log, rules,_filter_properties).encode('utf-8')
    logging.debug("reasoner is done")
    #logging.debug("reasoner: %s", reasoner_str)
        
    # Here is where we should be getting values from the reasoner
    reasoner_end_time = time.time()
    reasoner_end_size = mem("rss")

    current_memory_usage['reasoner_end_size'] = mem("rss")

    load_time = policyrunner.load_time
    policyrunner.load_time = 0
    load_size = policyrunner.load_size
    policyrunner.load_size = 0
     
    postload_time = policyrunner.postload_time
    policyrunner.postload_time = 0
    postload_size = policyrunner.postload_size
    policyrunner.postload_size = 0
     
    actual_time = policyrunner.actual_time
    policyrunner.actual_time = 0
    actual_size = policyrunner.actual_size
    policyrunner.actual_size = 0
     
    semantics_time = policyrunner.semantics_time
    policyrunner.semantics_time = 0

    semantics_parse_time = policyrunner.semantics_parse_time
    policyrunner.semantics_parse_time = 0
     
    reasoner_time = policyrunner.total_time
    policyrunner.total_time = 0
    reasoner_size = policyrunner.total_size
    policyrunner.total_size = 0

    #current_timings["log_generation_time"] = log_generated_time - context_load_time
    current_timings["log_generation_time"] = log_generated_time_end - log_generated_time_start 

    log_generation_time_val = log_generated_time_end - log_generated_time_start
    logging.debug("log generation time: " + str(log_generation_time_val))
    #current_timings["total_log_time"] = log_generated_time - start_time
    current_timings["total_log_time"] = current_timings["log_generation_time"]
    current_timings["reasoner_load_time"] = load_time 
    current_timings["reasoner_postload_time"] = postload_time
    current_timings["reasoner_actual_time"] = actual_time
    current_timings["reasoner_semantics_time"] = semantics_time
    current_timings["reasoner_semantics_parse_time"] = semantics_parse_time
    current_timings["reasoner_time_before_serialization"] = reasoner_time
    current_timings["reasoner_serialization_time"] = reasoner_end_time - log_generated_time_end - reasoner_time
    reasoner_serialization_value = current_timings["reasoner_serialization_time"]
    logging.debug("reasoner end time: " + str(reasoner_end_time))
    logging.debug("log generated time: " + str(log_generated_time))
    logging.debug("reasone time: " + str(reasoner_time))

    logging.debug("reasoner_serialization_time: " +
                  str(reasoner_serialization_value))
    current_timings["total_reasoner_time"] = reasoner_end_time - log_generated_time

    q.put((None, None))

    q.put(current_timings)

    #current_memory_usage["log_generation_size"] = log_generated_size - context_load_size
    current_memory_usage["log_generation_size"] = log_generated_memory_end - log_generated_memory_start
    #current_memory_usage["total_log_size"] = log_generated_size - start_size
    current_memory_usage["total_log_size"] = current_memory_usage["log_generation_size"]
    current_memory_usage["reasoner_load_size"] = load_size
    current_memory_usage["reasoner_postload_size"] = postload_size
    current_memory_usage["reasoner_actual_size"] = actual_size
    current_memory_usage["total_reasoner_size"] = reasoner_end_size - current_memory_usage["total_log_size"]

    q.put(current_memory_usage)
    
    #reasoner_str_list.append(reasoner_str)
    q.put((by_uri, data_uri, reasoner_str))

def run_reasoner(q, form):
    # q.put() should be used ONCE to write out the return value. It
    # should be a pair (type-string, response-content) OR (True,
    # current_times) to collect times over a number of runs.  The
    # (type-string, response-content) content will be returned by the
    # parent caller as a CGI response.

    #new_current_times: keep track of the timings in each reasoner invocation
    #actual_timings: calculate the overall timings to send for rendering


    start_time = 0
    context_load_time = 0
    log_generated_time = 0
    reasoner_end_time = 0
    now  = 0
    load_time = 0
    postload_time = 0
    actual_time = 0
    semantics_time = 0
    semantics_parse_time = 0
    reasoner_time = 0


    start_size = 0
    context_load_size = 0
    log_generated_size = 0
    reasoner_end_size = 0
    now_size = 0
    load_size = 0
    postload_size = 0
    actual_size = 0


    actual_timings = {}

    actual_timings["context_load_time"] = 0
    actual_timings["log_generation_time"] = 0
    actual_timings["total_log_time"] = 0
    actual_timings["reasoner_load_time"] = 0
    actual_timings["reasoner_postload_time"] = 0
    actual_timings["reasoner_actual_time"] = 0
    actual_timings["reasoner_semantics_time"] = 0 
    actual_timings["reasoner_semantics_parse_time"] = 0
    actual_timings["reasoner_time_before_serialization"] = 0
    actual_timings["reasoner_serialization_time"] = 0
    actual_timings["total_reasoner_time"] = 0
    actual_timings["legal_rendering_time"] = 0
    actual_timings["total_time"] = 0


    actual_memory_usage = {}

    actual_memory_usage["context_load_size"] = 0
    actual_memory_usage["log_generation_size"] = 0
    actual_memory_usage["total_log_size"] = 0
    actual_memory_usage["reasoner_load_size"] = 0
    actual_memory_usage["reasoner_postload_size"] = 0
    actual_memory_usage["reasoner_actual_size"] = 0
    actual_memory_usage["total_reasoner_size"] = 0
    actual_memory_usage["legal_rendering_size"] = 0
    actual_memory_usage["total_size"] = 0


    #actual_timings["context_load_time"] = context_load_time - start_time
    #actual_timings["log_generation_time"] = log_generated_time - context_load_time
    #actual_timings["total_log_time"] = log_generated_time - start_time
    #actual_timings["reasoner_load_time"] = load_time 
    #actual_timings["reasoner_postload_time"] = postload_time
    #actual_timings["reasoner_actual_time"] = actual_time
    #actual_timings["reasoner_semantics_time"] = semantics_time
    #actual_timings["reasoner_semantics_parse_time"] = semantics_parse_time
    #actual_timings["reasoner_time_before_serialization"] = reasoner_time
    #actual_timings[reasoner_serialization_time"] = reasoner_end_time - 
    #  log_generated_time - reasoner_time
    #actual_timings["total_reasoner_time"] = reasoner_end_time - log_generated_time
    #actual_timings["legal_rendering_time"] =now - reasoner_end_time
    #actual_timings["total_time"] = now - start_time

    #actual_memory_usage["context_load_size"] = context_load_size' - start_size
    #actual_memory_usage["log_generation_size"] = log_generated_size' - context_load_size
    #actual_memory_usage["total_log_size"] = log_generated_size - start_size
    #actual_memory_usage["reasoner_load_size"] = load_size
    #actual_memory_usage["reasoner_postload_size" = postload_size
    #actual_memory_usage["reasoner_actual_size"] = actual_size
    #actual_memory_usage["total_reasoner_size"] = reasoner_end_size - log_generated_size
    #actual_memory_usage["legal_rendering_size"] = now_size - reasoner_end_size
    #actual_memory_usage["total_size"] = now_size - start_size

    current_memory_stats = {}
    current_memory_stats['start_size'] = mem("rss")

    current_times = {}
    current_times['start_time'] = time.time()
    start_time = time.time()
    start_size = mem("rss")
         
    log_uris = form.getlist('logFile')
    log = form.getfirst('log')
    rules = form.getfirst('rules')

    rule_uri_input = form.getfirst('rulesFile')
    if not rule_uri_input:
        #return ('text/plain', "No rules files specified!")
        q.put(('text/plain', "No rules files specified!"))
        return

 
    rule_uris = []

    if '#Event' in rule_uri_input:
        logging.debug("processing rules")
        rule_uri_input_context = url_to_context(rule_uri_input)
        rule_uris = obtain_rule_uris_list(rule_uri_input_context)
    else:
        rule_uris.append(rule_uri_input)

    rules_contexts = [url_to_context(elem) for elem in rule_uris]
    logging.debug("rule_uris: %s and rules: %s", rule_uris, rules)



    see_also = []
    for context in rules_contexts:
        see_also.extend(evaluate_seealso(context))

    by_uri = form.getfirst('by')
    data_uri_input = form.getfirst('data')

    if not data_uri_input:
        #return ('text/plain', "No rules files specified!")
        q.put(('text/plain', "No data files specified!"))
        return
     
    
    data_uri_list = []
    
    if '#Event' in data_uri_input:
        logging.debug("processing data")
        data_uri_input_context = url_to_context(data_uri_input)
        data_uri_list = obtain_data_uris_list(data_uri_input_context)
    else:
        data_uri_list.append(data_uri_input)

    logging.debug("data uri list: %s", data_uri_list)
    logging.debug("size of data uri list: %s", len(data_uri_list))

    to_uri_input = form.getfirst('to')
    to_uri_list = []
    # TODO this is a clunky test, why was this done?
    if '#me' in to_uri_input or '#Person' in to_uri_input:
        to_uri_list.append(to_uri_input)
    elif '#Event' in to_uri_input:
        to_uri_input_context = url_to_context(to_uri_input)
        to_uri_list = obtain_to_uris_list(to_uri_input_context)
    else:
        logging.debug("ERROR with recipients format")
        #return ('text/plain', "Select one of the displayed recipients")
        q.put('text/plain', "Select one of the displayed recipients")
        return

    
    current_times['context_load_time'] = time.time()
    context_load_time = time.time()

    current_memory_stats['context_load_size'] = mem("rss")
    context_load_size = mem("rss")

    reasoner_str_list = []
    memory_usage_string = ""
    #### from here ####

    for to_uri in to_uri_list:
        for data_uri in data_uri_list:
            # Make ANOTHER process because each call to
            # policyrunner.testPolicy MUST be made in a separate
            # process, or the times will grow quadratically or worse
            # (due to state being saved in an unknown location).

            real_q = Queue()
            logging.debug("calling really_run_reasoner")
            p = Process(target=really_run_reasoner, args=(real_q, form, by_uri, to_uri, data_uri, rules_contexts, see_also, log_uris, rule_uris, log, rules))
            logging.debug("finished calling run_reasoner")
            p.start()
            retval = real_q.get()

            #start_rendering: is the start time from when we need to see how
            #long the rendering takes. Only the last value is needed (the last
            #time the reasoner is invoked. Thus, overwriting this value is ok.
            start_rendering = time.time()
            start_rendering_size = mem("rss")

            if retval[0] is not None:
                # Return because really_run_reasoner included a return
                # MIME type and value.
                q.put(retval)
                return
            else:
                # Collect the timings and memory usage from the reasoner.
                current_timings = real_q.get()
                current_memory_usage = real_q.get()
                output = real_q.get()
            
            p.join()

            actual_timings["context_load_time"] += context_load_time - start_time
            actual_timings["log_generation_time"] += current_timings["log_generation_time"]

            #actual_timings["total_log_time"] += log_generated_time - start_time
            actual_timings["total_log_time"] += current_timings["total_log_time"]
            # we still need to add in the context load time to the total log  time!
            actual_timings["reasoner_load_time"] += current_timings["reasoner_load_time"]
            actual_timings["reasoner_postload_time"] += current_timings["reasoner_postload_time"]
            actual_timings["reasoner_actual_time"] += current_timings["reasoner_actual_time"]
            actual_timings["reasoner_semantics_time"] += current_timings["reasoner_semantics_time"]
            actual_timings["reasoner_semantics_parse_time"] += current_timings["reasoner_semantics_parse_time"]
            actual_timings["reasoner_time_before_serialization"] += current_timings["reasoner_time_before_serialization"]
            actual_timings["reasoner_serialization_time"] += current_timings["reasoner_serialization_time"]
            actual_timings["total_reasoner_time"] += current_timings["total_reasoner_time"]


            actual_memory_usage["context_load_size"] += context_load_size - start_size
            #actual_memory_usage["log_generation_size"] += log_generated_size - context_load_size
            actual_memory_usage["log_generation_size"] += current_memory_usage["log_generation_size"]
            #actual_memory_usage["total_log_size"] += log_generated_size - start_size
            actual_memory_usage["total_log_size"] += current_memory_usage["total_log_size"]
            actual_memory_usage["reasoner_load_size"] += current_memory_usage["reasoner_load_size"]
            actual_memory_usage["reasoner_postload_size"] += current_memory_usage["reasoner_postload_size"]
            actual_memory_usage["reasoner_actual_size"] += current_memory_usage["reasoner_actual_size"]
            actual_memory_usage["total_reasoner_size"] += current_memory_usage["total_reasoner_size"]



            #reasoner_str_list.append(reasoner_str)
            reasoner_str_list.append((output[0], to_uri_input, output[1],
            rule_uri_input, output[2]))

    
    #### for loop to_uri ends  here ####

    #logging.debug("len of reasoner_str_list: %s", len(reasoner_str_list))
    #logging.debug("memory: %s", form.getfirst('memory'))


    html_output = render_law_multiple.render_law(
        reasoner_str_list, 'uri_str', rule_uris[0])

    finished_rendering = time.time()
    finished_rendering_size = mem("rss")

    # Note: these are not "aggregated" since rendering is done only once. 
    # Note: we can still use acttual start time because it is when the procesing
    # began
    actual_timings["legal_rendering_time"] = finished_rendering - start_rendering
    actual_timings["total_time"] = finished_rendering - start_time

    actual_memory_usage["legal_rendering_size"] += finished_rendering_size - start_rendering_size
    actual_memory_usage["total_size"] += finished_rendering_size - start_size

    # Adding the context load time to the total log time outside the for loops
    actual_timings["total_log_time"] += actual_timings["context_load_time"]
    actual_memory_usage["total_log_size"] += actual_memory_usage["context_load_size"]
    current_memory_stats['now_size'] = mem("rss")
   
    #current_times['size'] = `policy_store.size`


    global _store
    _store = llyn.RDFStore()

    show_flag = ''
    memory_flag = form.getfirst('show_memory')
    timings_flag = form.getfirst('show_timings')
    if memory_flag == 'true' and timings_flag == 'true':
        show_flag = 'both'
    elif memory_flag == 'true':
        show_flag = 'memory'
    elif timings_flag == 'true':
        show_flag = 'timing'

    if form.getfirst('use_tabulator') == 'true':
        if form.getfirst('debug'):
            header = 'text/plain'
        else:
            header = 'text/rdf+n3'
        #return (header, reasoner_str)
        #q.put((header, reasoner_str))
        q.put((header, reasoner_str_list[0][4]))
        return
    elif show_flag == 'timing':
        #q.put((True, current_times, 0))
        q.put((True, actual_timings, 0))
        return
    elif show_flag == 'memory':
        #q.put((True, 0, current_memory_stats))
        q.put((True, 0, actual_memory_usage))
        return
    elif show_flag == 'both':
        #q.put((True, current_times, current_memory_stats))
        q.put((True, actual_timings, actual_memory_usage))
        return
    #elif form.getfirst('memory') == 'true':

       #logging.debug("collecting memory stats")
       #header = 'text/plain'
       #current_memory_stats['reasoner_end_size'] = mem("rss")
       #html_output = render_law_multiple.render_law(
       #    reasoner_str_list, 'uri_str', rule_uris[0])
       #current_memory_stats['now_size'] = mem("rss")
       # 
       #current_memory_stats['load_size'] = policyrunner.load_size
       #policyrunner.load_size = 0
       #current_memory_stats['postload_size'] = policyrunner.postload_size
       #policyrunner.postload_size = 0
       #current_memory_stats['actual_size'] = policyrunner.actual_size
       #policyrunner.actual_size = 0
       #current_memory_stats['reasoner_size'] = policyrunner.total_size
       #policyrunner.total_size = 0
       #
       #logging.debug("completed memory stats")
       #output = "["
       #output += """ {
       #  "log_context_load": %(context_load_size)f,
       #  "log_generation": %(log_generation_size)f,
       #  "total_log": %(total_log_size)f,
       #  "reasoner_load": %(reasoner_load_size)f,
       #  "reasoner_postload": %(reasoner_postload_size)f,
       #  "reasoner_actual": %(reasoner_actual_size)f,
       #  "total_reasoner": %(total_reasoner_size)f,
       #  "legal_rendering": %(legal_rendering_size)f,
       #  "total": %(total_size)f,
       #},""" % (
       #  {"context_load_size": current_memory_stats['context_load_size'] -
       #                             current_memory_stats['start_size'],
       #   "log_generation_size": current_memory_stats['log_generated_size'] -
       #                             current_memory_stats['context_load_size'],
       #   "total_log_size": current_memory_stats['log_generated_size'] -
       #                             current_memory_stats['start_size'],
       #   "reasoner_load_size": current_memory_stats['load_size'],
       #   "reasoner_postload_size": current_memory_stats['postload_size'],
       #   "reasoner_actual_size": current_memory_stats['actual_size'],
       #   "total_reasoner_size": current_memory_stats['reasoner_end_size'] -
       #                             current_memory_stats['log_generated_size'],
       #   "legal_rendering_size": current_memory_stats['now_size'] -
       #                             current_memory_stats['reasoner_end_size'],
       #   "total_size": current_memory_stats['now_size'] -
       #                             current_memory_stats['start_size']})
       #output = output[:-1] + "]"

       #q.put(('text/plain', output))
       #return
    #elif form.getfirst('show_timings') == 'true':
       #logging.debug("in show_timings")

       #current_times['reasoner_end_time'] = time.time()
       #logging.debug("going to render_law")
       #html_output = render_law_multiple.render_law(
       #    reasoner_str_list, 'uri_str', rule_uris[0])
       #logging.debug("finished render_law")
       #
       #current_times['now'] = time.time()
       #
       #current_times['load_time'] = policyrunner.load_time
       #policyrunner.load_time = 0
       #current_times['postload_time'] = policyrunner.postload_time
       #policyrunner.postload_time = 0
       #current_times['actual_time'] = policyrunner.actual_time
       #policyrunner.actual_time = 0
       #current_times['semantics_time'] = policyrunner.semantics_time
       #policyrunner.semantics_time = 0
       #current_times['semantics_parse_time'] = policyrunner.semantics_parse_time
       #policyrunner.semantics_parse_time = 0
       #current_times['reasoner_time'] = policyrunner.total_time
       #policyrunner.total_time = 0
       #current_times['size'] = `policy_store.size`
       #
       #global _store
       #_store = llyn.RDFStore()
       #logging.debug("completed show_timings")
       ## First argument is True to continue the loop.
       #q.put((True, current_times))
       #return
    else:
        html_output = render_law_multiple.render_law(
            reasoner_str_list, 'uri_str', rule_uris[0])
        #return ('text/html', html_output)
        q.put(('text/html', html_output))
        return

def generate_output(form):
    logging.debug("In generate_output")
    times = []
    memory_stats = []
 
    runs = 1
    try:
        runs = int(form.getfirst('runs'))
    except:
        runs = 1

    for i in range(runs):
        logging.debug("running run %s", i)
        # Use multiprocessing to get a clean slate for each reasoning
        # round (because policyrunner leaves cruft for each round).
        q = Queue()
        logging.debug("calling run_reasoner")
        p = Process(target=run_reasoner, args=(q, form))
        logging.debug("finished calling run_reasoner")
        p.start()
        retval = q.get()
        p.join()
        if retval[0] == True:
            # Concatenating times and continue loop
            # Second argument: timing
            # Third argument: memory
            if retval[1] != 0:
                times.append(retval[1])
            if retval[2] != 0:
                memory_stats.append(retval[2])
        else:
            # It's actually an HTTP response pair.
            return retval

    # show_timings
    #header = 'application/json'
    header = 'text/plain'
    output_times = """ "times": ["""
    for actual_timings in times:
        output_times += """
{
    "log_context_load": %(context_load_time)f,
    "log_generation": %(log_generation_time)f,
    "total_log": %(total_log_time)f,
    "reasoner_load": %(reasoner_load_time)f,
    "reasoner_postload": %(reasoner_postload_time)f,
    "reasoner_actual": %(reasoner_actual_time)f,
    "reasoner_semantics": %(reasoner_semantics_time)f,
    "reasoner_semantics_parse": %(reasoner_semantics_parse_time)f,
    "reasoner_before_serialization": %(reasoner_time_before_serialization)f,
    "reasoner_serialization": %(reasoner_serialization_time)f,
    "total_reasoner": %(total_reasoner_time)f,
    "legal_rendering": %(legal_rendering_time)f,
    "total": %(total_time)f,
},""" % (
        {"context_load_time": actual_timings['context_load_time'],
         "log_generation_time": actual_timings['log_generation_time'],
         "total_log_time": actual_timings['total_log_time'],
         "reasoner_load_time": actual_timings['reasoner_load_time'],
         "reasoner_postload_time": actual_timings['reasoner_postload_time'],
         "reasoner_actual_time": actual_timings['reasoner_actual_time'],
         "reasoner_semantics_time": actual_timings['reasoner_semantics_time'],
         "reasoner_semantics_parse_time":
                        actual_timings['reasoner_semantics_parse_time'],
         "reasoner_time_before_serialization":
                        actual_timings['reasoner_time_before_serialization'],
         "reasoner_serialization_time":
                        actual_timings['reasoner_serialization_time'],
         "total_reasoner_time": actual_timings['total_reasoner_time'],
         "legal_rendering_time": actual_timings['legal_rendering_time'],
         "total_time": actual_timings['total_time']})
    output_times = output_times[:-1] + "]"

    output_memory_stats = """ "memory_stats": ["""
    for actual_memory_usage in memory_stats:
        output_memory_stats += """ 
{
    "log_context_load": %(context_load_size)f,
    "log_generation": %(log_generation_size)f,
    "total_log": %(total_log_size)f,
    "reasoner_load": %(reasoner_load_size)f,
    "reasoner_postload": %(reasoner_postload_size)f,
    "reasoner_actual": %(reasoner_actual_size)f,
    "total_reasoner": %(total_reasoner_size)f,
    "legal_rendering": %(legal_rendering_size)f,
    "total": %(total_size)f
},""" % (
        {"context_load_size": actual_memory_usage['context_load_size'],
         "log_generation_size": actual_memory_usage['log_generation_size'],
         "total_log_size": actual_memory_usage['total_log_size'],
         "reasoner_load_size": actual_memory_usage['reasoner_load_size'],
         "reasoner_postload_size": actual_memory_usage['reasoner_postload_size'],
         "reasoner_actual_size": actual_memory_usage['reasoner_actual_size'],
         "total_reasoner_size": actual_memory_usage['total_reasoner_size'],
         "legal_rendering_size": actual_memory_usage['legal_rendering_size'],
         "total_size": actual_memory_usage['total_size']})
    output_memory_stats = output_memory_stats[:-1] + "]"

    output = ''
    if retval[1] != 0 and retval[2] != 0:
        output = "{" + output_times + "," + output_memory_stats + "}"
    elif retval[1] != 0:
        output = "{" + output_times + "}"
    elif retval[2] != 0:
        output = "{" + output_memory_stats + "}"

    logging.debug("completed generate_output")
    return (header, output)

def main_wsgi():
    import wsgiref.handlers
    wsgiref.handlers.CGIHandler().run(wsgi_app)

def wsgi_app(environ, start_response):
    form = cgi.FieldStorage(fp=environ['wsgi.input'], environ=environ)

    try:
        type, content = generate_output(form)
        start_response('200 OK', [('Content-Type', type),
                                  ('Content-Length', str(len(content)))])
        yield content
    except:
        error_log = ''.join(traceback.format_exception(
            sys.exc_type, sys.exc_value, sys.exc_traceback))
        start_response('500 Internal Server Error',
                       [('Content-Type', 'text/plain'),
                        ('Content-Length', str(len(error_log)))])
        yield error_log

def main():
    sys.setrecursionlimit(3000);
    stdout_ptr = sys.stdout
    sys.stdout = StringIO.StringIO()
    form = cgi.FieldStorage()

    if form.getfirst('reasoner'):
        reasoner = form.getfirst('reasoner')
    else:
        reasoner = 'classic'

    global policyrunner, llyn, RDFSink, SUBJ, PRED, OBJ, uripath
    if reasoner == 'classic':
        from cwmrete.tmswap import policyrunner
        from cwmrete.tmswap import llyn
        from cwmrete.tmswap import RDFSink
        from cwmrete.tmswap.RDFSink import SUBJ, PRED, OBJ
        from cwmrete.tmswap import uripath
    else:
        # NOTE: When adding a reasoner, please make sure to add the
        # global "load_time", "postload_time", "actual_time" and "total_time"
        # properties to policyrunner.py
        if reasoner == 'latest':
            sys.path.insert(0, './reasoners/latest/')
        from tmswap import policyrunner
        from tmswap import llyn
        from tmswap import RDFSink
        from tmswap.RDFSink import SUBJ, PRED, OBJ
        from tmswap import uripath
 
    global _store
    _store = llyn.RDFStore()


    try:
        header, content = generate_output(form)
        stdout_ptr.write(format_headers(header, content))
    except:
        error_log = ''.join(traceback.format_exception(
            sys.exc_type, sys.exc_value, sys.exc_traceback))
        stdout_ptr.write(format_headers('text/plain', error_log))

if __name__ == "__main__":
    main()
