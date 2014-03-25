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
# Scyther commands with caching.
#
# Main functions:
#
#   doScytherCommand
#   getScytherBackend
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
from Misc import *

#---------------------------------------------------------------------------

"""
Globals
"""

SCYTHERBIN = None

#---------------------------------------------------------------------------

"""
Get current directory (for this file)
"""
def getMyDir():
    return os.path.dirname( os.path.realpath( __file__ ) )

"""
The default path for the binaries is the current one.
"""
def getBinDir():
    return getMyDir()

"""
Return Cache prefix path
Returns None if not existent
"""
def getCacheDir():
    
    tmpdir = None

    # Check if user chose the path
    cachedirkey = "SCYTHERCACHEDIR"
    if cachedirkey in os.environ.keys():
        tmpdir = os.environ[cachedirkey]
        if tmpdir == "":
            # Special value: if the variable is present, but equals the empty string, we disable caching.
            return None
    else:
        # Otherwise take from path
        tmpdir = tempfile.gettempdir()
    
    # If not none, append special name
    if tmpdir != None:
        tmpdir = os.path.join(tmpdir,"Scyther-cache")

    return tmpdir

    
#---------------------------------------------------------------------------

def checkSanity(program):
    """
    This is where the existence is checked of the Scyther backend.
    """

    if not os.path.isfile(program):
        raise Error.BinaryError, program

#---------------------------------------------------------------------------

def getScytherBackend():
    # Where is my executable?
    #
    # Auto-detect platform and infer executable name from that
    #
    global SCYTHERBIN

    if SCYTHERBIN == None:

        if "linux" in sys.platform:

            """ linux """
            scythername = "scyther-linux"

        elif "darwin" in sys.platform:

            """ OS X """
            scythername = "scyther-mac"

        elif sys.platform.startswith('win'):

            """ Windows """
            scythername = "scyther-w32.exe"

        else:

            """ Unsupported"""
            raise Error.UnknownPlatformError, sys.platform

        program = os.path.join(getBinDir(),scythername)

        # Check if it makes sense and propagate if so.
        checkSanity(program)
        SCYTHERBIN = program

    return SCYTHERBIN


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

def doScytherCommandReal(spdl, args):
    """ 
    Run Scyther backend on the input
    
    Arguments:
        spdl -- string describing the spdl text
        args -- arguments for the command-line
    Returns:
        (output,errors)
        output -- string which is the real output
        errors -- string which captures the errors
    """

    program = getScytherBackend()

    # Sanitize input somewhat
    if spdl == "":
        # Scyther hickups on completely empty input
        spdl = "\n"

    # Generate temporary files for the output.
    # Requires Python 2.3 though.
    (fde,fne) = tempfile.mkstemp()  # errors
    (fdo,fno) = tempfile.mkstemp()  # output
    if spdl:
        (fdi,fni) = tempfile.mkstemp()  # input

        # Write (input) file
        fhi = os.fdopen(fdi,'w+b')
        fhi.write(spdl)
        fhi.close()

    # Generate command line for the Scyther process
    cmd = ""
    cmd += "\"%s\"" % program
    cmd += " --append-errors=%s" % fne
    cmd += " --append-output=%s" % fno
    cmd += " %s" % args
    if spdl:
        cmd += " %s" % fni

    # Start the process
    safeCommand(cmd)

    # reseek
    fhe = os.fdopen(fde)
    fho = os.fdopen(fdo)
    errors = fhe.read()
    output = fho.read()

    # clean up files
    fhe.close()
    fho.close()
    os.remove(fne)
    os.remove(fno)
    if spdl:
        os.remove(fni)

    return (output,errors)

#---------------------------------------------------------------------------

def doScytherCommand(spdl, args, checkKnown=False,useCache=True):
    """
    Cached version of the 'real' command before.

    TODO: CC: One possible problem with the caching is the side-effect, e.g., scyther writing to specific named output files. These are not
    captured in the cache. I don't have a good solution for that yet.
    """
    global HASHLIB

    # Can we use the cache?
    canCache = False
    if HASHLIB:
        cacheDir = getCacheDir()
        if cacheDir != None:
            canCache = True
    else:
        cacheDir = None

    # But if the users says no, it's no
    if useCache == False:
        canCache = False

    # If we cannot use the cache, we either need to compute or, if checking for cache presense,...
    if not canCache:
        if checkKnown == True:
            # not using the cache, so we don't have it already
            return False
        else:
            # Need to compute
            return doScytherCommandReal(spdl,args)

    # Apparently we are supposed to be able to use the cache
    m = hashlib.sha256()
    if spdl == None:
        m.update("[spdl:None]")
    else:
        m.update(spdl)
    if args == None:
        m.update("[args:None]")
    else:
        m.update(args)

    uid = m.hexdigest()

    # Split the uid to make 256 subdirectories with 256 subdirectories...
    prefixlen = 2
    uid1 = uid[:prefixlen]
    uid2 = uid[prefixlen:prefixlen+2]
    uid3 = uid[prefixlen+2:]

    # Possibly we could also decide to store input and arguments in the cache to analyze things later

    # Construct: cachePath/uid1/uid2/...
    path = os.path.join(cacheDir,uid1,uid2)
    name1 = "%s.out" % (uid3)
    name2 = "%s.err" % (uid3)

    fname1 = os.path.join(path, name1)
    fname2 = os.path.join(path, name2)

    try:
        """
        Try to retrieve the result from the cache
        """
        fh1 = open(fname1,"r")
        out = fh1.read()
        fh1.close()
        fh2 = open(fname2,"r")
        err = fh2.read()
        fh2.close()
        if checkKnown == True:
            # We got to here, so we have it
            return True
        else:
            # Not checking cache, we need the result
            return (out,err)
    except:
        pass

    """
    Something went wrong, do the real thing and cache afterwards
    """
    if checkKnown == True:
        # We were only checking, abort
        return False

    (out,err) = doScytherCommandReal(spdl,args)

    try:
        # Try to store result in cache
        ensurePath(path)

        fh1 = open(fname1,"w")
        fh1.write(out)
        fh1.close()

        fh2 = open(fname2,"w")
        fh2.write(err)
        fh2.close()
    except:
        pass

    return (out,err)

#---------------------------------------------------------------------------

# vim: set ts=4 sw=4 et list lcs=tab\:>-:
