import { useState, useMemo, useCallback } from 'react';

interface Paper {
  slug: string;
  title: string;
  authors: string;
  year: number;
  number: number;
  category: string;
  keywords: string[];
  crawler: string;
}

interface PapersMeta {
  years: number[];
  categories: { name: string; count: number }[];
  total: number;
}

interface Props {
  papers: Paper[];
  meta: PapersMeta;
}

const CATEGORY_COLORS: Record<string, string> = {
  Foundations: 'bg-purple-900/60 text-purple-300',
  'Secret-key cryptography': 'bg-amber-900/60 text-amber-300',
  'Public-key cryptography': 'bg-blue-900/60 text-blue-300',
  'Cryptographic protocols': 'bg-green-900/60 text-green-300',
  'Attacks and cryptanalysis': 'bg-red-900/60 text-red-300',
  Applications: 'bg-cyan-900/60 text-cyan-300',
  Implementation: 'bg-orange-900/60 text-orange-300',
  Uncategorized: 'bg-gray-800/60 text-gray-400',
};

function categoryColor(cat: string): string {
  return CATEGORY_COLORS[cat] || CATEGORY_COLORS['Uncategorized'];
}

export default function PapersList({ papers, meta }: Props) {
  const [search, setSearch] = useState('');
  const [selectedYears, setSelectedYears] = useState<Set<number>>(new Set());
  const [selectedCategories, setSelectedCategories] = useState<Set<string>>(
    new Set()
  );

  const toggleYear = useCallback((year: number) => {
    setSelectedYears((prev) => {
      const next = new Set(prev);
      if (next.has(year)) {
        next.delete(year);
      } else {
        next.add(year);
      }
      return next;
    });
  }, []);

  const toggleCategory = useCallback((cat: string) => {
    setSelectedCategories((prev) => {
      const next = new Set(prev);
      if (next.has(cat)) {
        next.delete(cat);
      } else {
        next.add(cat);
      }
      return next;
    });
  }, []);

  const clearAll = useCallback(() => {
    setSearch('');
    setSelectedYears(new Set());
    setSelectedCategories(new Set());
  }, []);

  const hasFilters =
    search.length > 0 || selectedYears.size > 0 || selectedCategories.size > 0;

  const filtered = useMemo(() => {
    const q = search.toLowerCase().trim();
    return papers.filter((p) => {
      if (selectedYears.size > 0 && !selectedYears.has(p.year)) {
        return false;
      }
      const cat = p.category || 'Uncategorized';
      if (selectedCategories.size > 0 && !selectedCategories.has(cat)) {
        return false;
      }
      if (q) {
        const haystack = `${p.title} ${p.authors}`.toLowerCase();
        return q.split(/\s+/).every((w) => haystack.includes(w));
      }
      return true;
    });
  }, [papers, search, selectedYears, selectedCategories]);

  return (
    <div>
      {/* Search */}
      <div className="mb-4">
        <input
          type="text"
          placeholder="Search by title or authors..."
          value={search}
          onChange={(e) => setSearch(e.target.value)}
          className="w-full px-4 py-2 bg-gray-800 border
            border-gray-700 rounded-lg text-sm text-gray-200
            placeholder-gray-500 focus:outline-none
            focus:border-blue-500"
        />
      </div>

      {/* Year pills */}
      <div className="mb-3 flex flex-wrap gap-1.5">
        {meta.years.map((year) => (
          <button
            key={year}
            onClick={() => toggleYear(year)}
            className={`px-2.5 py-0.5 rounded-full text-xs
              transition-colors cursor-pointer ${
                selectedYears.has(year)
                  ? 'bg-blue-600 text-white'
                  : 'bg-gray-800 text-gray-400 hover:bg-gray-700'
              }`}
          >
            {year}
          </button>
        ))}
      </div>

      {/* Category chips */}
      <div className="mb-4 flex flex-wrap gap-1.5">
        {meta.categories.map(({ name, count }) => (
          <button
            key={name}
            onClick={() => toggleCategory(name)}
            className={`px-2.5 py-0.5 rounded-full text-xs
              transition-colors cursor-pointer ${
                selectedCategories.has(name)
                  ? categoryColor(name) + ' ring-1 ring-white/30'
                  : 'bg-gray-800 text-gray-400 hover:bg-gray-700'
              }`}
          >
            {name} ({count})
          </button>
        ))}
      </div>

      {/* Results count + clear */}
      <div
        className="mb-4 flex items-center gap-3 text-sm
        text-gray-400"
      >
        <span>
          Showing {filtered.length} of {papers.length} papers
        </span>
        {hasFilters && (
          <button
            onClick={clearAll}
            className="text-blue-400 hover:text-blue-300 text-xs
              cursor-pointer"
          >
            Clear all filters
          </button>
        )}
      </div>

      {/* Paper list */}
      {filtered.length === 0 ? (
        <div className="py-12 text-center text-gray-500">
          <p className="mb-3">No papers match your filters.</p>
          <button
            onClick={clearAll}
            className="text-blue-400 hover:text-blue-300 text-sm
              cursor-pointer"
          >
            Clear all filters
          </button>
        </div>
      ) : (
        <div className="border-t border-gray-800">
          {filtered.map((paper) => {
            const cat = paper.category || 'Uncategorized';
            return (
              <a
                key={paper.slug}
                href={`/papers/${paper.slug}`}
                className="block px-2 py-3 border-b
                  border-gray-800 hover:bg-gray-800/50
                  transition-colors"
              >
                <div
                  className="flex items-start justify-between
                  gap-3"
                >
                  <h3
                    className="text-sm font-medium text-gray-200
                      leading-snug flex-1 min-w-0"
                    dangerouslySetInnerHTML={{
                      __html: paper.title,
                    }}
                  />
                  <div
                    className="flex items-center gap-2
                    shrink-0 mt-0.5"
                  >
                    <span
                      className="bg-gray-700 text-gray-300
                      text-xs px-2 py-0.5 rounded-full"
                    >
                      {paper.year}
                    </span>
                    <span
                      className={`text-xs px-2 py-0.5
                        rounded-full whitespace-nowrap
                        ${categoryColor(cat)}`}
                    >
                      {cat}
                    </span>
                  </div>
                </div>
                <p
                  className="text-xs text-gray-500 mt-0.5
                  truncate"
                >
                  {paper.authors}
                </p>
              </a>
            );
          })}
        </div>
      )}
    </div>
  );
}
