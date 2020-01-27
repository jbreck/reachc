import choraconfig, glob, os.path

batch = choraconfig.clone_batch("cfind_spacergt")

batch["toolIDs"] = ["cfind",
                    "cfind_refine",
                    "spacer471"]
batch["timeout"] = 300
batch["instant_error_callouts"] = True
batch["instant_unsound_callouts"] = True
