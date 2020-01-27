import choraconfig, glob, os.path

batch = choraconfig.clone_batch("reachc_spacergt")

batch["toolIDs"] = ["reachc",
                    "reachc_refine",
                    "spacer471"]
batch["timeout"] = 300
batch["instant_error_callouts"] = True
batch["instant_unsound_callouts"] = True
