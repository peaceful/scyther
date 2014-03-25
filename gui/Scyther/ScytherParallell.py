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

#---------------------------------------------------------------------------

""" Import externals """
import os
import os.path
import sys
import StringIO

#---------------------------------------------------------------------------

""" Import scyther components """
import XMLReader
import Error
import Claim
from ScytherCached import getScytherBackend,doScytherCommand
from Misc import *

#---------------------------------------------------------------------------

"""
Globals
"""

#---------------------------------------------------------------------------

def doScytherVerify(spdl=None,args="",checkKnown=False,useCache=True,xml=True):
    """ Should return a list of results.

        If checkKnown == True, we do not call Scyther, but just check the cache, and return True iff the result is in the cache.
        If useCache == False, don't use the cache at all.

        return (output,claims,myerrors,mywarnings)
    """

    # We do want XML output in any case
    xargs = "--xml-output %s" % args

    # execute
    result = doScytherCommand(spdl, xargs, checkKnown=checkKnown,useCache=useCache)

    # If we are using checkKnown, we're only looking for a boolean result.
    if checkKnown == True:
        return result

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

    return (output,claims,myerrors,mywarnings)

#---------------------------------------------------------------------------

# vim: set ts=4 sw=4 et list lcs=tab\:>-:
