"""Build helpers local to the Lean/POSIX binding package."""

load("@rules_lean//lean:defs.bzl", "LeanInfo")

def _lean_generated_c_file_impl(ctx):
    matches = [
        file
        for file in ctx.attr.dep[LeanInfo].c_files.to_list()
        if file.short_path.endswith(ctx.attr.module_suffix)
    ]
    if len(matches) != 1:
        fail(
            "expected exactly one generated Lean C file ending in %r, found %s" %
            (ctx.attr.module_suffix, [file.short_path for file in matches]),
        )
    return [DefaultInfo(files = depset(matches))]

lean_generated_c_file = rule(
    implementation = _lean_generated_c_file_impl,
    attrs = {
        "dep": attr.label(mandatory = True, providers = [LeanInfo]),
        "module_suffix": attr.string(mandatory = True),
    },
)
