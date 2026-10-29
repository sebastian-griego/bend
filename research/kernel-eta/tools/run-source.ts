// Set BENDTT after any caller-supplied Bun environment wrapper.
const [kernel, script, ...args] = process.argv.slice(2);
const child = Bun.spawn([process.execPath, "--no-env-file", script, ...args], {
  env: {...process.env, BENDTT: kernel, PAR: "4"},
  stdin: "ignore", stdout: "inherit", stderr: "inherit",
});
process.exit(await child.exited);
