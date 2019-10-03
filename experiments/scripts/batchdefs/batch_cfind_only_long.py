import choraconfig, glob, os.path

batch = choraconfig.clone_batch("cfind_spacergt")

batch["toolIDs"] = ["cfind"]
batch["timeout"] = 300
batch["instant_error_callouts"] = True
batch["instant_unsound_callouts"] = True
