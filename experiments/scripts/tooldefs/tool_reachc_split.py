import choraconfig, os.path

tool = choraconfig.clone_tool("reachc")
tool["displayname"] = "ReACHC:split"
tool["shortname"] = "reachc:split"
tool["cmd"] = [tool["root"] + "/reachc.native","-split-loops","{filename}"]
