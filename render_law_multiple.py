#!/usr/bin/python

from __future__ import with_statement

import sys
import tempfile
from string import Template
from optparse import OptionParser

from tmswap import llyn
from tmswap.RDFSink import SUBJ, PRED, OBJ
from tmswap import uripath

import logging
logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)

_RENDER_DEBUG_LEVEL = 0

_html_template_str = """
<!DOCTYPE HTML PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html id="docHTML">
<head>
    <title>${page_title}</title>
    <meta http-equiv="content-type" content="text/html; charset=ISO-8859-1">
    <link type="text/css" href="/css/simpletab.css" rel="stylesheet">

    <script type="text/javascript" language="JavaScript">
     function ToggleContent(d) {
        var text_element = document.getElementById("td_"+d);
        var img_element = document.getElementById("img_"+d);
        if (text_element.getAttribute('style') == 'display: none;') {
            img_element.setAttribute('src', "/img/tbl-collapse.png" )
            text_element.setAttribute('style', 'display:block');
        } else {
            img_element.setAttribute('src', "/img/tbl-expand-trans.png" )
            text_element.setAttribute('style', 'display:none');
    }}
    </script>
</head>
<body>

<table id="outline"><tr style="vertical-align: top;"><td class="obj" about="${outline_title}">
    <table style="background-color: white;"><tr><td>
        <img title="Hide details." alt="collapse" src="/img/tbl-collapse.png">
        <strong>${outline_title}<img class="paneShown" title="Lawyer's View" alt="Lawyer's View" src="/img/law.jpg"></strong>
    </td></tr></table>
</td></tr></table>

<div class="title" id="div_issue">
<table><tr>
    <td><a href="javascript:ToggleContent('1')">
    <img id="img_1" src="/img/tbl-collapse.png"></a></td>
    <td>Issue:</td>
</tr></table>
</div>
<div class="irfac" id="td_1">
<table><tr>
    <td> </td>
    <td>Whether a dissemination of <a href="${data_uri}">${data_uri}</a> by <a
    href="${by_uri}">${by_uri}</a> to <a href="${to_uri}">${to_uri}</a> is
    compliant with law?</td>
</tr></table>
</div>

<div class="title" id="div_rule">
<table><tr>
    <td><a href="javascript:ToggleContent('2')">
    <img id="img_2" src="/img/tbl-collapse.png"></a></td>
    <td>Rule:</td></tr>
</table></div>
<div class="irfac" id="td_2">
<table><tr>
    <td> </td>
    <td>The issue will be decided under <a href="${rule_uri}">${rule_uri}</a></td>
</tr></table>
</div>

<div class="title" id="div_results">
<table><tr>
    <td><a href="javascript:ToggleContent('3')">
    <img id="img_3" src="/img/tbl-collapse.png"></a></td>
    <td>Results:</td></tr>
</table></div>
<div class="irfac" id="td_3">
<table><tr>
    <td> </td>
    ${results}
</tr></table>
</div>

</body>
</html>
"""

_html_template_str_inner = """
<table><tr>
    <td><a href="javascript:ToggleContent('${analysis_index}')">
    <img id="img_${analysis_index}" src="/img/tbl-collapse.png"></a></td>
    <td>Analysis ${results_index}:</td>
</tr></table>
<div class="irfac" id="td_${analysis_index}">
<table><tr>
    <td> </td>
    <td><table><tr><td><ul>
    ${analysis}
    </ul></td></tr></table></td>
</tr></table></div>

<table><tr>
    <td><a href="javascript:ToggleContent('${conclusion_index}')">
    <img id="img_${conclusion_index}" src="/img/tbl-collapse.png"></a></td>
    <td>Conclusion ${results_index}:</td>
</tr></table>
<div class="irfac" id="td_${conclusion_index}">
<table><tr>
    <td> </td>
    <td><table><tr><td><ul>
    ${conclusion}
    </ul></td></tr></table></td>
</tr></table></div>
"""

_html_template = Template(_html_template_str)

_html_template_inner = Template(_html_template_str_inner)

_rdfs_prefix = "http://www.w3.org/2000/01/rdf-schema"
_air_prefix = "http://dig.csail.mit.edu/TAMI/2007/amord/air"
_tms_prefix = "http://dig.csail.mit.edu/TAMI/2007/amord/tms"

_label_predicate = "%s#label" % _rdfs_prefix

_air_compliant_with = "%s#compliant-with" % _air_prefix
_air_non_compliant_with = "%s#non-compliant-with" % _air_prefix
_tms_justify = "%s#justification" % _tms_prefix
_tms_description = "%s#description" % _tms_prefix
_tms_rule_name = "%s#rule-name" % _tms_prefix
_tms_premise = "%s#premise" % _tms_prefix

_store = llyn.RDFStore()
_canonical_name_cache = {}

def url_to_context(url):
    try:
        context = _store.load(uripath.splitFrag(url)[0],
                              remember = 0, referer = '', topLevel = True)
        context.reopen()
        context.stayOpen = 1
        return context
    except:
        return None

def str_to_context(rdf_literal):
    f = tempfile.NamedTemporaryFile()
    f.write(rdf_literal)
    f.flush()
    context = url_to_context("file://%s" % f.name)
    f.close()
    return context

def get_stmts_matching(context, subj=None, pred=None, obj=None):
    term_dict = {}
    if subj: subj = context.newSymbol(subj)
    if pred: pred = context.newSymbol(pred)
    if obj: obj = context.newSymbol(obj)

    stmt_bindings = context.statementsMatching(subj=subj, pred=pred, obj=obj)
    for elem in stmt_bindings:
        term_dict[elem[SUBJ]] = elem[OBJ]
    return term_dict

def url_to_canonical_name(url):
    if url in _canonical_name_cache:
        return _canonical_name_cache[url]

    context = url_to_context(url)
    if context:
        label_pred = context.newSymbol(_label_predicate)
        url_sym = context.newSymbol(url)
        label = context.statementsMatching(subj=url_sym, pred=label_pred)
        if not label:
            return_val = url
        else:
            return_val = str(label[0][OBJ])
    else:
        return_val = url

    _canonical_name_cache[url] = return_val
    return return_val

def render_symbol(obj):
    if _RENDER_DEBUG_LEVEL > 3:
        template = 'SYMBOL: <a href="%s">%s</a>'
    else:
        template = '<a href="%s">%s</a>'
    return template % (obj.uriref(), obj.debugString())

def render_fragment(obj):
    #logging.debug("obj: %s ", obj)
    #logging.debug("obj.uriref: %s ", obj.uriref())
    
    #logging.debug("url_to_canonical_name: %s ", url_to_canonical_name(obj.uriref()).split("#")[-1])
    if _RENDER_DEBUG_LEVEL > 3:
        template = 'FRAGMENT: <a href="%s">%s</a>'
    else:
        template = '<a href="%s">%s</a>'
    return template % (obj.uriref(), url_to_canonical_name(obj.uriref()).split("#")[-1])

def render_literal(obj):
    return obj.value()

def render_subjects(subjects):
    #logging.debug("subjects: %s ", subjects)
    output = []
    template = '\t\t<li class="irfac_li"><div>'
    for item in subjects:
        #logging.debug("item: %s ", item)
        output.append(template)
        for element in item:
            #logging.debug("element: %s ", element)
            #logging.debug("type of element: %s ", type(element))
            if type(element).__name__ == "Symbol":
                output.append(render_symbol(element))
            elif type(element).__name__ == "Literal":
                output.append(render_literal(element))
            elif type(element).__name__ == "Fragment": 
                output.append(render_fragment(element))
        output.append("</div></li>\n")
    #logging.debug("render_subjects function done")
    return '\n'.join(output)
    
def render_conclusions(conclusions):
    output = []
    template = ('\t\t<tr><td>The transaction - </td>'
                '<td><a href="%s">%s</a></td><td> is </td>'
                '<td>%s</td><td><a href="%s">%s</a></td></tr>')
    for item in conclusions:
        con_context = item.context()
        con_subj = item.subject()
        con_pred = item.predicate()
        con_obj = item.object()
        output.append(template % (con_subj.uriref(), url_to_canonical_name(con_subj.uriref()).split("#")[-1],
                                  str(con_pred).split(":")[-1],
                                  con_obj.uriref(), url_to_canonical_name(con_obj.uriref())))
    output.append("</td></tr>\n")
    return ''.join(output)
    
def render_outline(uri):
    return _outline_template % (uri, uri)

def render_justify_debug(justify_stmts):
    output = []
    for stmt in justify_stmts:
        output.append("<li><ul><li>Subject Type: %s</li><li>Subject: %s</li>"
                      "<li>Object Type: %s</li><li>Object: %s</li></ul></li>\n"
                      % (type(stmt).__name__, stmt.debugString(),
                         type(justify_stmts[stmt]).__name__,
                         justify_stmts[stmt].debugString())) 
    return ''.join(output)

def render_law(justifications = None, uri = None, policy = None):

    by_uri = ''
    to_uri = ''
    data_uri = ''
    rule_uri = ''
    
    logging.debug("in render_law")
    analysis_output = []

    results_index = 1

    analysis_index_placeholder = 4 #analysis div starts with 4
    conclusion_index_placeholder = 5 #conclusion div starts with 5

    html_inner_str = ""

    for justification_str in justifications:

        by_uri = justification_str[0]
        to_uri = justification_str[1]
        data_uri = justification_str[2]
        rule_uri = justification_str[3] 
        justification = justification_str[4]
        logging.debug("rendering")
        #logging.debug("%s ", justification)
        source_context = str_to_context(justification)

        justify_stmts = get_stmts_matching(source_context, pred=_tms_justify)
        description_stmts = get_stmts_matching(source_context, pred=_tms_description)

        analyses = []
        descriptions = []
        justifications = []
        conclusions = []

        rules_dict = {}

        for key in description_stmts:
            if type(key).__name__ == "IndexedFormula":
                if type(description_stmts[key]).__name__ == "NonEmptyList":
                    analyses.append(description_stmts[key])
            if type(key).__name__ == "AnonymousExistential":
                if type(description_stmts[key]).__name__ == "NonEmptyList":
                   descriptions.append(description_stmts[key])

        #logging.debug("description")

        for stmt in filter(lambda x: type(x).__name__ == "IndexedFormula",
                       justify_stmts):
            # This will extract our conclusions from the justification statements.
            for clause in stmt:
                context = clause.context()
                compliant_pred = context.newSymbol(_air_compliant_with)
                non_compliant_pred = context.newSymbol(_air_non_compliant_with)
                foo = clause.predicate()
                if foo == compliant_pred or foo == non_compliant_pred:
                    conclusions.append(clause)
            # This will extract the remaining rules relevant to the justification(s).
            if type(justify_stmts[stmt]).__name__ =="AnonymousExistential":
                rule_name_pred = source_context.newSymbol(_tms_rule_name)
                premise_pred = source_context.newSymbol(_tms_premise)
                justify_pred = source_context.newSymbol(_tms_justify)
                tmp_bindings = source_context.statementsMatching(subj=justify_stmts[stmt], pred=rule_name_pred)
                if _RENDER_DEBUG_LEVEL > 5:
                    for debug_rule in tmp_bindings:
                        rules_dict[debug_rule[SUBJ]] = debug_rule[OBJ]
                rule_name_found = tmp_bindings[0]
                term_condition = source_context.statementsMatching(subj=rule_name_found, pred=rule_name_pred, obj=premise_pred)
                while term_condition == None :
                    currrent_rule = source_context.statementsMatching(obj=rule_name_found)
                    this_rule = current_rule.popitem()
                    if type(this_rule[OBJ]).__name__ == "NonEmptyList":
                        descriptions.append(this_rule[OBJ])
                    # Hack copied from Tabulator to fix the rule appearing instead of
                    # the bnode (AnonymousExistential) containing the description
                    correct_current_rule = []
                    for rule in current_rule:
                        if type(rule).__name__ == "AnonymousExistential":
                            correct_current_rule = rule
                        break
                    current_rule_stmts = source_context.statementsMatching(subj=correct_current_rule, pred=justify_pred)
                    first_rule = current_rule_stmts.popitem()
                    next_rule_stmts = source_context.statementsMatching(first_rule[OBJ], pred=rule_name_pred, obj=premise_pred)
                    the_next_rule = next_rule_stmts.popitem()
                    rule_name_found = the_next_rule[OBJ]
                    term_condition = source_context.statementsMatching(subj=rule_name_found, pred=justify_pred, obj=premise_pred)

        #logging.debug("finished loops")


        html_output = []

        if _RENDER_DEBUG_LEVEL > 5:
            html_output.append("<li>Justifications</li>")
            html_output.append(render_justify_debug(justify_stmts))
            html_output.append("<li>Rule Statements</li>")
            html_output.append(render_justify_debug(rules_dict))
            html_output.append("<li>The Rest</li>")
      
        #logging.debug("level > 5 done")
       
        if descriptions:
            if _RENDER_DEBUG_LEVEL > 1: 
                html_output.append("<li>Descriptions</li>")
            html_output.append(render_subjects(descriptions))
        
        #logging.debug("descriptions done")

        if analyses:
            analyses.reverse()
            #logging.debug("analyses.reverse() done")
            if _RENDER_DEBUG_LEVEL > 1: 
                html_output.append("<li>Analyses</li>")
            html_output.append(render_subjects(analyses))
            #logging.debug("render_subjects(analyses) done")

        #logging.debug("analyses done")

        if conclusions: conclusions.reverse()

        #logging.debug("finished rendering")
        
        #analysis_output.append(html_output)
        #analysis_output.append({'analysis': html_output, 'conclusions': conclusions})

        substitutions_inner = {
            'analysis_index': analysis_index_placeholder,
            'conclusion_index': conclusion_index_placeholder,
            'results_index': results_index,
            'analysis': '\n'.join(html_output),
            'conclusion': render_conclusions(conclusions),
        }
        html_inner_str += _html_template_inner.substitute(substitutions_inner)

        results_index += 1
        analysis_index_placeholder += 2
        conclusion_index_placeholder += 2

    substitutions_outer = {
        'page_title': "Reasoner Output: Lawyer View",
        'outline_title': uri,
        'results': html_inner_str,
        #'analysis': '\n'.join(html_output),
        #'analysis': '\n'.join(analysis_output),
        #'conclusion': render_conclusions(conclusions),
        'transaction_uri': uri,
        'policy_uri': policy,
        'policy_str': url_to_canonical_name(policy),
        'by_uri': by_uri,
        'to_uri': to_uri,
        'data_uri': data_uri,
        'rule_uri': rule_uri,
    }

    return _html_template.substitute(substitutions_outer)
    #return _html_template_new

# Tests specify 3 values: justification path, uri, policy
_known_tests = {
    'bill' : ( '/home/wdc/DIG/logfiles/2a-newclean.n3',
               'http://dice.csail.mit.edu/dhs_air.py?by=http://dig.csail.mit.edu/2010/DHS-fusion/US/DHS/profiles/FredAgenti#me&to=http://dig.csail.mit.edu/2010/DHS-fusion/MA/profiles/MiaAnalysa#me&data=http://dig.csail.mit.edu/2010/DHS-fusion/US/DHS/documents/Fake_DHS_Response.pdf&rulesFile=http://dig.csail.mit.edu/2010/DHS-fusion/US/DHS/rules/5_USC_552a.n3',
               'http://dig.csail.mit.edu/2010/DHS-fusion/US/DHS/rules/5_USC_552a.n3' ),
    'sam' : ( '/Users/samuelsw/Downloads/dhs_air.py',
               'http://dice.csail.mit.edu/dhs_air.py?by=http://dig.csail.mit.edu/2010/DHS-fusion/US/DHS/profiles/FredAgenti#me&to=http://dig.csail.mit.edu/2010/DHS-fusion/MA/profiles/MiaAnalysa#me&data=http://dig.csail.mit.edu/2010/DHS-fusion/US/DHS/documents/Fake_DHS_Response.pdf&rulesFile=http://dig.csail.mit.edu/2010/DHS-fusion/US/DHS/rules/5_USC_552a.n3',
               'http://dig.csail.mit.edu/2010/DHS-fusion/US/DHS/rules/5_USC_552a.n3' )
    }

def main():
    usage = "usage: %prog testName"
    parser = OptionParser(usage)
    (options, args) = parser.parse_args()

    if not args:
        test = "sam"
    else:
        test = args[0]
        
    justification_path, uri, policy = _known_tests[test]

    with open(justification_path) as f:
        justification_str = f.read()

    print render_law(justification = justification_str, uri = uri, policy = policy)

if __name__ == "__main__":
    main()
