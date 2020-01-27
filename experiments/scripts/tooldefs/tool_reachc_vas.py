import choraconfig, os.path

tool = choraconfig.clone_tool("cfind")
tool["displayname"] = "CFIND:vas"
tool["shortname"] = "cfind:vas"
tool["cmd"] = [tool["root"] + "/cfind.native","-vas","{filename}"]
