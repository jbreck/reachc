import choraconfig, os.path

tool = choraconfig.clone_tool("reachc")
tool["displayname"] = "ReACHC:vas"
tool["shortname"] = "reachc:vas"
tool["cmd"] = [tool["root"] + "/reachc.native","-vas","{filename}"]
