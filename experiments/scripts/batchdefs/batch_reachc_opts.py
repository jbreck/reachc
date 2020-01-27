import choraconfig, glob, os.path

batch = choraconfig.clone_batch("cfind_spacergt")

batch["toolIDs"] = ["cfind",
                    "cfind_split",
                    "cfind_refine",
                    "cfind_prsdpg",
                    "cfind_vas",
                    "cfind_vass",
                    "spacer471"]
batch["timeout"] = 30
batch["instant_error_callouts"] = True
batch["instant_unsound_callouts"] = True
