import choraconfig, re, sys, os.path

def spacer_assert_results(params) :
    if "logpath" not in params : 
        print "ERROR: spacer_assert_results was called without a path"
        sys.exit(0)
    #e.g., "Assertion on line 13 FAILED"
    results = list()
    kind_dict = {"sat":"SAT","unsat":"UNSAT","UNKNOWN":"UNKNOWN"}
    regex = "(\\S+)"
    with open(params["logpath"],"rb") as logfile :
        for line in logfile :
            matches = re.match(regex, line)
            if matches :
                for kind in kind_dict :
                    if kind in matches.group(1) :
                        results.append( (kind_dict[kind], -1) )
                        break
                #else :
                #    results.append( ("UNRECOGNIZED", -1 ) )
            else :
                pass
    return results

tool = choraconfig.get_default_tool_dict() 
tool["root"] = "/u/j/b/jbreck/.opam/4.06.1/bin" #choraconfig.specify_tool_root_requirement("cfind","cfind.native")
tool["displayname"] = "SPACER"
tool["cmd"] = ["z3","{filename}"]
tool["assert_results"] = spacer_assert_results
tool["error_callout"] = choraconfig.generic_error_callout

