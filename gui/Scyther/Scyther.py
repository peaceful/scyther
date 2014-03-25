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
# Scyther interface
#

#---------------------------------------------------------------------------

""" Import externals """
import os
import os.path
import sys
import StringIO
import tempfile
try:
    import hashlib
    HASHLIB = True
except ImportError:
    HASHLIB = False
    pass

#---------------------------------------------------------------------------

""" Import scyther components """
import XMLReader
import Error
import Claim
from ScytherCached import getScytherBackend,doScytherCommand
from ScytherParallell import doScytherVerify
from Misc import *

#---------------------------------------------------------------------------

"""
Globals
"""

#---------------------------------------------------------------------------

def Check():
    """
    Perform sanity check on Scyther backend.
    """
    program = getScytherBackend()   # Raises an error if the backend is not found or is not executable

#---------------------------------------------------------------------------

def EnsureString(x,sep=" "):
    """
    Takes a thing that is either a list or a string.
    Turns it into a string. If it was a list, <sep> is inserted, and the
    process iterats.

    TODO does not accept unicode yet, that is something that must be
    handled to or we run into wxPython problems eventually.
    """
    if type(x) is str:
        return x

    elif type(x) is list:
        newlist = []
        for el in x:
            newlist.append(EnsureString(el,sep))
        return sep.join(newlist)

    else:
        raise Error.StringListError, x


#---------------------------------------------------------------------------

class Scyther(object):
    def __init__ ( self):

        # Init
        self.program = getScytherBackend()
        self.spdl = None
        self.inputfile = None
        self.filenames = []
        self.options = ""
        self.claims = None
        self.errors = None
        self.errorcount = 0
        self.warnings = None
        self.output = None
        self.cmd = None

    def setInput(self,spdl):
        self.spdl = spdl
        self.inputfile = None
        self.guessFileNames()

    def setFile(self,filename):
        self.inputfile = filename
        self.filenames = [self.inputfile]
        self.spdl = ""
        fp = open(filename,"r")
        for l in fp.readlines():
            self.spdl += l
        fp.close()

    def addFile(self,filename):
        self.inputfile = None
        if not self.spdl:
            self.spdl = ""
        fp = open(filename,"r")
        for l in fp.readlines():
            self.spdl += l
        fp.close()
        self.guessFileNames()

    def guessFileNames(self,spdl=None):
        """
        Try to extract filenames (well, actually, protocol names) sloppily from some spdl script.

        There are two modes:

        [init] : If the spdl parameter is empty or None, we reset the filenames and extract from self.spdl
        [add]  : If the spdl parameter is non-empty, add the extracted filenames to an existing list

        """

        if (spdl == None) or (len(spdl) == 0):
            spdl = self.spdl
            if spdl == None:
                spdl = ""
            self.filenames = []

        for sl in spdl.splitlines():
            l = sl.strip()
            prefix = "protocol "
            postfix = "("
            x = l.find(prefix)
            if x >= 0:
                # The prefix occurs
                y = l.find(postfix,x+len(prefix))
                if y >= 0:
                    gn = l[x+len(prefix):y]
                    # check for helper protocols
                    if not gn.startswith("@"):
                        if gn not in self.filenames:
                            self.filenames.append(gn)

    def addArglist(self,arglist):
        for arg in arglist:
            self.options += " %s" % (arg)

    def sanitize(self):
        """ Sanitize some of the input """
        self.options = EnsureString(self.options)

    def verify(self,extraoptions=None,checkKnown=False,useCache=True):
        """ Should return a list of results.

            If checkKnown == True, we do not call Scyther, but just check the cache, and return True iff the result is in the cache.
            If useCache == False, don't use the cache at all.
        """

        # Cleanup first
        self.sanitize()
    
        # prepare arguments
        args = " --dot-output --plain"
        args += " %s" % self.options
        if extraoptions:
            # extraoptions might need sanitizing
            args += " %s" % EnsureString(extraoptions)

        # Do the actual verification
        (output,claims,errors,warnings) = doScytherVerify(self.spdl,args,checkKnown=checkKnown,useCache=useCache)

        self.errors = errors
        self.warnings = warnings

        # Raise an error in case of trouble
        self.errorcount = len(self.errors)
        if self.errorcount > 0:
            raise Error.ScytherError(self.errors,filenames=self.filenames,options=self.options)

        self.claims = claims
        self.output = output

        if claims != None:
            return claims
        else:
            return output


    def verifyOne(self,cl=None,checkKnown=False):
        """
        Verify just a single claim with an ID retrieved from the
        procedure below, 'scanClaims', or a full claim object

        If checkKnown is True, return if the result is already known (but never recompute).
        """
        if cl:
            # We accept either a claim or a claim id
            if isinstance(cl,Claim.Claim):
                cl = cl.id
            return self.verify("--filter=%s" % cl, checkKnown=checkKnown)
        else:
            # If no claim, then its just normal verification
            return self.verify(checkKnown=checkKnown)

    def scanClaims(self):
        """
        Retrieve the list of claims. Of each element (a claim), claim.id
        can be passed to --filter=X or 'verifyOne' later.
        A result of 'None' means that some errors occurred.
        """
        self.verify("--scan-claims")
        if self.errorcount > 0:
            return None
        else:
            return self.claims

    def getClaim(self,claimid):
        if self.claims:
            for cl in self.claims:
                if cl.id == claimid:
                    return cl
        return None

    def __str__(self):
        if self.errorcount > 0:
            return "%i errors:\n%s" % (self.errorcount, "\n".join(self.errors))
        else:
            if self.claims != None:
                s = "Verification results:\n"
                for cl in self.claims:
                    s += str(cl) + "\n"
                return s
            else:
                return self.output

#---------------------------------------------------------------------------

def GetClaims(filelist, filterlist=None):
    """
    Given a list of file names in filelist,
    returns a dictionary of filenames to lists claim names.
    Filenames which yielded no claims are filtered out.
    
    Filterlist may be None or a list of claim names (Secret, SKR, Niagree etc).
    """

    dict = {}
    for fname in filelist:
        try:
            sc = Scyther()
            sc.setFile(fname)
            l = sc.scanClaims()
            if l != None:
                cl = []
                for claim in l:
                    if filterlist == None:
                        cl.append(claim.id)
                    else:
                        if claim.claimtype in filterlist:
                            cl.append(claim.id)
                dict[fname] = cl
        except:
            pass
    return dict

#---------------------------------------------------------------------------

def FindProtocols(path="",filterProtocol=None):
    """
    Find a list of protocol names

    Note: Unix only! Will not work under windows.
    """

    import commands

    cmd = "find %s -iname '*.spdl'" % (path)
    plist = commands.getoutput(cmd).splitlines()
    nlist = []
    for prot in plist:
        if filterProtocol != None:
            if filterProtocol(prot):
                nlist.append(prot)
        else:
            nlist.append(prot)
    return nlist

#---------------------------------------------------------------------------

def GetInfo(html=False):
    """
    Retrieve a tuple (location,string) with information about the tool,
    retrieved from the --expert --version data
    """

    program = getScytherBackend()
    arg = "--expert --version"
    (output,errors) = doScytherCommand(spdl=None, args=arg)
    if not html:
        return (program,output)
    else:
        sep = "<br>\n"
        html = "Backend: %s%s" % (program,sep)
        for l in output.splitlines():
            l.strip()
            html += "%s%s" % (l,sep)
        return html


def GetLicense():
    """
    Retrieve license information.
    """

    arg = "--license"
    (output,errors) = doScytherCommand(spdl=None, args=arg)
    return output


#---------------------------------------------------------------------------

# vim: set ts=4 sw=4 et list lcs=tab\:>-:
