import choraconfig, os.path

tool = choraconfig.clone_tool("reachc")
tool["displayname"] = "ReACHC:refine"
tool["shortname"] = "reachc:refine"
tool["cmd"] = [tool["root"] + "/reachc.native","-refine","{filename}"]
