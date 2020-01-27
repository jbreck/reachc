import choraconfig, os.path

tool = choraconfig.clone_tool("cfind")
tool["displayname"] = "CFIND:refine"
tool["shortname"] = "cfind:refine"
tool["cmd"] = [tool["root"] + "/cfind.native","-refine","{filename}"]
