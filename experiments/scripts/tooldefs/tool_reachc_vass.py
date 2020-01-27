import choraconfig, os.path

tool = choraconfig.clone_tool("reachc")
tool["displayname"] = "ReACHC:vass"
tool["shortname"] = "reachc:vass"
tool["cmd"] = [tool["root"] + "/reachc.native","-vass","{filename}"]
