import choraconfig, os.path

tool = choraconfig.clone_tool("cfind")
tool["displayname"] = "CFIND:vass"
tool["shortname"] = "cfind:vass"
tool["cmd"] = [tool["root"] + "/cfind.native","-vass","{filename}"]
