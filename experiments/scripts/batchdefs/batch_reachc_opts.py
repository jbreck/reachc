import choraconfig, glob, os.path

batch = choraconfig.clone_batch("reachc_spacergt")

batch["toolIDs"] = ["reachc",
                    "reachc_split",
                    "reachc_refine",
                    "reachc_prsdpg",
                    "reachc_vas",
                    "reachc_vass",
                    "spacer471"]
batch["timeout"] = 30
batch["instant_error_callouts"] = True
batch["instant_unsound_callouts"] = True
