import {readFile, writeFile} from 'fs/promises';
import {join as pathJoin, dirname} from 'path';
import {fileURLToPath} from 'url';

const __dirname = dirname(fileURLToPath(import.meta.url));

const sources = [
    // TypeScript syntax (2.81MB)
    {
        url: 'https://raw.githubusercontent.com/microsoft/TypeScript/v5.3.3/src/compiler/checker.ts',
        allocSize: 16,
    },
    // Real world app tsx (1.0M)
    {
        url: 'https://raw.githubusercontent.com/oxc-project/benchmark-files/main/cal.com.tsx',
        allocSize: 8,
    },
    // Real world content-heavy app jsx (3K)
    {
        url: 'https://raw.githubusercontent.com/oxc-project/benchmark-files/main/RadixUIAdoptionSection.jsx',
        allocSize: 1,
    },
    // Heavy with classes (554K)
    {
        url: 'https://cdn.jsdelivr.net/npm/pdfjs-dist@4.0.269/build/pdf.mjs',
        allocSize: 8,
    },
    // ES5 (3.9M)
    {
        url: 'https://cdn.jsdelivr.net/npm/antd@5.12.5/dist/antd.js',
        allocSize: 32
    },
];

// Same directory as Rust benchmarks use for downloaded files
const cacheDirPath = pathJoin(__dirname, '../../target');

export default await Promise.all(sources.map(async ({url, allocSize}) => {
    const filename = url.split('/').at(-1),
        path = pathJoin(cacheDirPath, filename);

    let sourceBuff, sourceStr;
    try {
        sourceBuff = await readFile(path);
        sourceStr = sourceBuff.toString();
    } catch {
        const res = await fetch(url);
        sourceStr = await res.text();
        sourceBuff = Buffer.from(sourceStr);
        await writeFile(path, sourceBuff);
    }

    // Convert from MiB to bytes
    allocSize *= 1024 * 1024;

    return {filename, sourceBuff, sourceStr, allocSize};
}));