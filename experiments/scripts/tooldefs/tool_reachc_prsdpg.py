import choraconfig, os.path

tool = choraconfig.clone_tool("cfind")
tool["displayname"] = "CFIND:prsdpg"
tool["shortname"] = "cfind:prsdpg"
tool["cmd"] = [tool["root"] + "/cfind.native","-prsd-pg","{filename}"]
