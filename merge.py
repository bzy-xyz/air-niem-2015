import lxml
import lxml.etree
import rdflib
import sys
import os
import re
import argparse
import tempfile
import itertools

ns_rdfify = u'http://dig.csail.mit.edu/2014/rdfify/schema#'

import rdfify
from rdfify import rdfify2, xml2rdf, xsd2rdfs

from rdfify.builtin_types import builtInDatatypeNames

def merge(files, additional_xml_schemata):
    g = rdflib.Graph()
    s = rdflib.Graph()
    sdata = rdfify2.SchemaData()
    
    for f in files:
        # we support two types of files:
        # - RDF graphs in n3 format
        # - XML documents non-RDF (typically NIEM)
        
        # first try to read in the file as ordinary n3
        try:
            tmp = rdflib.Graph()
            tmp.parse(f, format='n3')
            g.parse(f, format='n3')
        # if this doesn't work, then we try to invoke the XML logic
        except:
            try:
                tr = lxml.etree.parse(f)
                r = tr.getroot()
                rdfify2.extractRDFGraphWithSchemaInPlace(g, s, sdata, r, additional_xml_schemata, f.split('#')[0])
            # if even that doesn't work, give up
            except:
                raise
                
    return (g, s)

def main():
    argparser = argparse.ArgumentParser()
    argparser.add_argument('-s','--include-xml-schema', action='append')
    argparser.add_argument('-o','--outfile',default=None)
    argparser.add_argument('infile', nargs='+')
    
    args = argparser.parse_args()
    
    g, s = merge(args.infile, args.include_xml_schema, args.outfile if args.outfile else "")
    
    #print "exporting"
    
    stmp = tempfile.NamedTemporaryFile()
    gtmp = tempfile.NamedTemporaryFile(delete=False)


    stmp.write(s.serialize(format='n3'))
    gtmp.write(g.serialize(format='n3'))

    stmp.flush()
    gtmp.flush()

    # Then merge the two graphs
    g = rdflib.Graph()
    g.parse(stmp.name, format='n3')
    g.parse(gtmp.name, format='n3')
    
    o = open(args.outfile, 'w')
    
    o.write(g.serialize(format='n3'))
    
if __name__ == "__main__":
    main()
