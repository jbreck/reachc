import choraconfig, re, sys, os.path

def reachc_assert_results(params) :
    if "logpath" not in params : 
        print "ERROR: reachc_assert_results was called without a path"
        sys.exit(0)
    #e.g., "Assertion on line 13 FAILED"
    results = list()
    kind_dict = {"SAT":"SAT","UNSAT":"UNSAT","UNKNOWN":"UNKNOWN"}
    regex = "RESULT: (\\S+)"
    with open(params["logpath"],"rb") as logfile :
        for line in logfile :
            matches = re.match(regex, line)
            if matches :
                for kind in kind_dict :
                    if kind in matches.group(1) :
                        results.append( (kind_dict[kind], -1) )
                        break
                else :
                    results.append( ("UNRECOGNIZED", -1 ) )
    return results

tool = choraconfig.get_default_tool_dict() 
tool["root"] = choraconfig.specify_tool_root_requirement("reachc","reachc.native")
tool["displayname"] = "ReACHC"
tool["cmd"] = [tool["root"] + "/reachc.native","{filename}"]
tool["assert_results"] = reachc_assert_results
tool["error_callout"] = choraconfig.generic_error_callout

