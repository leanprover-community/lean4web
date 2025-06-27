#!/usr/bin/env node

import { readdirSync, lstatSync, existsSync } from 'fs';
import { resolve, join } from 'path';
import { spawnSync } from 'child_process';

// Change to ../Projects directory relative to this script
const baseDir = resolve(__dirname, '../Projects');
process.chdir(baseDir);
const isWin = process.platform === 'win32';
const buildScriptName = isWin ? 'build.cmd' : 'build.sh';

// Iterate over subfolders in Projects
readdirSync('.').forEach(folder => {
  const folderPath = join(baseDir, folder);

  if (lstatSync(folderPath).isDirectory()) {

    const buildScriptPath = join(folderPath, buildScriptName);

    if (existsSync(buildScriptPath)) {
      const start = Date.now();

      console.log(`Start building ${folder}`);
      if (!isWin) {
        spawnSync('logger', ['-t', 'lean4web', `Start building ${folder}`]);        
      }

      // Run the build script
      const result = spawnSync('bash', [buildScriptPath], { stdio: 'inherit' });

      const duration = Math.floor((Date.now() - start) / 1000);
      const minutes = Math.floor(duration / 60);
      const seconds = duration % 60;

      console.log(`Finished ${folder} in ${minutes}:${seconds < 10 ? '0' : ''}${seconds} min`);
      if (!isWin) {
        spawnSync('logger', ['-t', 'lean4web', `Finished ${folder} in ${minutes}:${seconds < 10 ? '0' : ''}${seconds} min`]);
      }
    } else {
      console.log(`Skipping ${folder}: ${buildScriptName} missing`);
    }
  }
});