import choraconfig, glob, os.path

batch = choraconfig.clone_batch("reachc_spacergt")

batch["toolIDs"] = ["reachc"]
batch["timeout"] = 300
batch["instant_error_callouts"] = True
batch["instant_unsound_callouts"] = True
