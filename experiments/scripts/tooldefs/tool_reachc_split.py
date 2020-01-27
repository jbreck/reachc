import choraconfig, os.path

tool = choraconfig.clone_tool("cfind")
tool["displayname"] = "CFIND:split"
tool["shortname"] = "cfind:split"
tool["cmd"] = [tool["root"] + "/cfind.native","-split-loops","{filename}"]
