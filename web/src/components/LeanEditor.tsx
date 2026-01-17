import { useState } from 'react';

interface LeanEditorProps {
  /** Initial Lean code to display */
  code: string;
  /** Height of the editor (default: 400px) */
  height?: string;
  /** Project to use on the server (optional) */
  project?: string;
  /** Whether the editor is read-only (shows just output) */
  readOnly?: boolean;
}

/**
 * Embeds a lean4web editor for running Lean code in the browser.
 * Uses live.lean-lang.org as the backend server.
 *
 * @see https://github.com/leanprover-community/lean4web
 */
export function LeanEditor({
  code,
  height = '400px',
  project,
  readOnly = false,
}: LeanEditorProps) {
  const [isLoading, setIsLoading] = useState(true);

  // Build the URL with parameters
  const baseUrl = 'https://live.lean-lang.org';
  const params = new URLSearchParams();

  // Settings (query params before #)
  params.set('theme', 'dark');
  params.set('wordWrap', 'true');

  // Build hash params for code
  const hashParams: string[] = [];

  // Use plain code parameter (lean4web handles escaping)
  hashParams.push(`code=${encodeURIComponent(code)}`);

  if (project) {
    hashParams.push(`project=${encodeURIComponent(project)}`);
  }

  const url = `${baseUrl}/?${params.toString()}#${hashParams.join('&')}`;

  return (
    <div className="lean-editor-container my-6">
      <div className="flex items-center justify-between bg-gray-700 px-4 py-2 rounded-t-lg">
        <span className="text-sm text-gray-300 font-mono">Lean 4</span>
        <a
          href={url}
          target="_blank"
          rel="noopener noreferrer"
          className="text-xs text-blue-400 hover:text-blue-300"
        >
          Open in new tab ↗
        </a>
      </div>
      <div className="relative" style={{ height }}>
        {isLoading && (
          <div className="absolute inset-0 flex items-center justify-center bg-gray-800 text-gray-400">
            Loading Lean editor...
          </div>
        )}
        <iframe
          src={url}
          className="w-full h-full border-0 rounded-b-lg"
          title="Lean 4 Editor"
          onLoad={() => setIsLoading(false)}
          sandbox="allow-scripts allow-same-origin allow-popups allow-forms"
        />
      </div>
      {readOnly && (
        <p className="text-xs text-gray-500 mt-2">
          This example is read-only. Open in a new tab to edit.
        </p>
      )}
    </div>
  );
}
