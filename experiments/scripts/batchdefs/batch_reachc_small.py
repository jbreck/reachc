import choraconfig, glob, os.path

batch = choraconfig.get_default_batch_dict()

batch["root"] = os.path.join(choraconfig.get_tool_root("reachc"), "experiments/benchmarks/small/")
batch["files"] = glob.glob(batch["root"] + "*.smt2")
batch["format_style"] = "assert"
batch["toolIDs"] = ["reachc","spacer471"]
#batch["format_col_width_proportional"] = True
batch["timeout"] = 10

