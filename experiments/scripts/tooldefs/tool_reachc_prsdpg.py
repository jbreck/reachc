import choraconfig, os.path

tool = choraconfig.clone_tool("reachc")
tool["displayname"] = "ReACHC:prsdpg"
tool["shortname"] = "reachc:prsdpg"
tool["cmd"] = [tool["root"] + "/reachc.native","-prsd-pg","{filename}"]
