#!/usr/bin/python
"""
	Scyther : An automatic verifier for security protocols.
	Copyright (C) 2007-2013 Cas Cremers

	This program is free software; you can redistribute it and/or
	modify it under the terms of the GNU General Public License
	as published by the Free Software Foundation; either version 2
	of the License, or (at your option) any later version.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with this program; if not, write to the Free Software
	Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
"""

#
# Scyther verification interface
# This part handles the parallellisation (if any)
#
# Main functions:
#
#   doScytherVerify
#
# An optional file 'pparams.txt' indicates the parallellistion parameters,
# where the first line contains the worker count (set 0 to get cpu_count), the
# modulus, and the prefix length, separated by space.
#

#---------------------------------------------------------------------------

""" Import externals """
import os
import os.path
import sys
import StringIO
from multiprocessing import Pool, cpu_count

#---------------------------------------------------------------------------

""" Import scyther components """
import XMLReader
import Error
import Claim
from ScytherCached import getScytherBackend,doScytherCommand
from Misc import *
from ScytherResult import makeScytherResult

#---------------------------------------------------------------------------

"""
Globals
"""

#---------------------------------------------------------------------------

def doScytherVerifyWorker((spdl,args,checkKnown,useCache)):
    """ Should return a list of results.

        If checkKnown == True, we do not call Scyther, but just check the cache, and return True iff the result is in the cache.
        If useCache == False, don't use the cache at all.

        return ScytherResult object
    """

    # We do want XML output in any case
    xargs = "--xml-output %s" % args

    # execute
    result = doScytherCommand(spdl, xargs, checkKnown=checkKnown,useCache=useCache)

    # If we are using checkKnown, we get a boolean result.
    if isinstance(result,bool):
        return makeScytherResult(result)

    # Otherwise the result should be a pair
    (output,errors) = result

    # process errors
    myerrors = []
    mywarnings = []
    for l in errors.splitlines():
        line = l.strip()
        if len(line) > 0:
            # filter out any non-errors (say maybe only claim etc) and count
            # them.
            if line.startswith("claim\t"):
                # Claims are lost, reconstructed from the XML output
                pass
            elif line.startswith("warning"):
                # Warnings are stored seperately
                mywarnings.append(line)
            else:
                # otherwise it is an error
                myerrors.append(line)

    # process output
    claims = None
    if len(output) > 0:
        if output.startswith("<scyther>"):

            # whoohee, xml
            xmlfile = StringIO.StringIO(output)
            reader = XMLReader.XMLReader()
            claims = reader.readXML(xmlfile)

    return makeScytherResult((output,claims,myerrors,mywarnings))

#---------------------------------------------------------------------------

def generateChoices(modulus,seqlen,prefix=[]):
    """
    Generate switch prefixes
    """
    if len(prefix) >= seqlen:

        return ["--prefix-filter=%i:%s" % (modulus,",".join(map(str,prefix)))]

    else:
        res = []
        for i in range(0,modulus):
            res = res + generateChoices(modulus,seqlen,prefix + [i])
        return res

#---------------------------------------------------------------------------

def getParameters():
    """
    Return the modulus and the sequence length
    """
    M = cpu_count()     # TODO: May raise NotImplementedError, ignoring for now.
    N = 2
    ln = 6
    try:
        fp = open("pparams.txt",'r')
        l = fp.readlines()
        dt = l[0].split()   # split first line according to spaces
        Mtry = int(dt[0])
        if Mtry > 0:
            M = Mtry
        N = int(dt[1])
        ln = int(dt[2])
        #print "Read parameters:", M, N, ln
        fp.close()
    except None:
        pass

    return (M,N,ln)

#---------------------------------------------------------------------------

def doScytherVerify(spdl=None,args="",checkKnown=False,useCache=True):
    """
    Interface to wrap the parallellisation

    TODO: Ideally the cache should wrap around the parallellisation, to avoid forking. Now it is the other way around.
    """
    if checkKnown == True:
        # Nothing to parallellise for cache checking
        return doScytherVerifyWorker((spdl,args,checkKnown,useCache))

    # From this point on we assume the worker returns a four-tuple.
    
    (M,N,ln) = getParameters()
    switchlist = generateChoices(N,ln)
    arglist = []
    for sw in switchlist:
        arglist.append((spdl,"%s %s" % (args,sw),checkKnown,useCache))

    pool = Pool(M)
    reslist = pool.map(doScytherVerifyWorker,arglist)

    res = None
    for ires in reslist:
        ires.merge(res)
        res = ires
    return res

    #res = None
    #for sw in switchlist:
    #    print "Prefix filter:", sw
    #    newres = doScytherVerifyWorker(spdl=spdl,args="%s %s" % (args,sw),checkKnown=checkKnown,useCache=useCache)
    #    newres.merge(res)
    #    res = newres
    #return res




#---------------------------------------------------------------------------

# vim: set ts=4 sw=4 et list lcs=tab\:>-:
