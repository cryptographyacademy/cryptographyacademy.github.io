# Visual Regression Tests

This directory contains visual regression tests for the Cryptography Academy website using Playwright.

## Overview

Visual regression testing helps catch unintended UI/UX changes by comparing screenshots of pages against baseline images. These tests run automatically on every PR to ensure visual consistency.

## Running Tests

### Prerequisites

Install Playwright browsers (first time only):
```bash
npx playwright install
```

### Run All Visual Tests

```bash
# From the web directory
npm test

# Or from the project root
make test-visual
```

### Run Tests for Specific Browser/Viewport

```bash
npm run test -- --project=chromium-desktop
npm run test -- --project=chromium-mobile
npm run test -- --project=firefox-desktop
npm run test -- --project=webkit-desktop
```

### Run Tests in UI Mode (Interactive)

```bash
npm run test:ui
```

This opens an interactive UI where you can:
- See visual diffs side-by-side
- Run specific tests
- Debug failing tests
- Approve new baselines

## Updating Baseline Screenshots

When you intentionally change the UI, you'll need to update the baseline screenshots:

```bash
# Update all baselines
npm run test:update-snapshots

# Update baselines for a specific project
npm run test -- --project=chromium-desktop --update-snapshots

# Update baselines for a specific test file
npm run test -- tests/visual/pages.spec.ts --update-snapshots
```

After updating baselines, commit the new screenshots:
```bash
git add tests/visual/__screenshots__/
git commit -m "Update visual regression baselines"
```

## Test Coverage

### Pages Tested

- **Homepage** - Hero section, navigation, feature cards, footer
- **Setup Page** - Installation and configuration guide
- **Foundations Page** - Mathematical foundations content
- **Primitives Page** - Cryptographic primitives overview
- **Proofs Page** - Zero-knowledge proofs content
- **About Page** - Project information

### Components Tested

- Navigation bar (desktop and mobile)
- Footer
- Hero sections
- Feature cards

### Viewport Sizes

- **Mobile**: 375px × 667px
- **Tablet**: 768px × 1024px
- **Desktop**: 1280px × 720px
- **Large Desktop**: 1920px × 1080px

### Browsers

- Chromium (primary)
- Firefox (optional)
- WebKit/Safari (optional)

## CI Integration

Visual regression tests run automatically on every PR via GitHub Actions. The CI workflow:

1. Builds the site
2. Starts a preview server
3. Runs visual regression tests
4. Fails the build if screenshots don't match baselines
5. Uploads test reports as artifacts for review

## How It Works

1. **First Run**: Creates baseline screenshots stored in `tests/visual/__screenshots__/`
2. **Subsequent Runs**: Takes new screenshots and compares pixel-by-pixel with baselines
3. **Differences**: If differences exceed threshold, test fails and generates a diff image
4. **Review**: Developers review diffs to determine if changes are intentional or bugs

## Configuration

Test configuration is in `playwright.config.ts`. Key settings:

- **Snapshot Path Template**: Where screenshots are stored
- **Timeout**: 30 seconds per test
- **Retries**: 2 retries on CI, 0 locally
- **Web Server**: Automatically builds and serves the site before tests

## Troubleshooting

### Tests fail with "Screenshot comparison failed"

This means the current rendering doesn't match the baseline. Either:
1. A visual regression was introduced (bug) - fix the code
2. The change is intentional - update baselines with `npm run test:update-snapshots`

### Tests timeout

- Increase timeout in `playwright.config.ts`
- Check if the dev server is starting properly
- Ensure port 4321 is available

### Flaky tests (intermittent failures)

- Add more `waitForTimeout` calls to ensure page is fully rendered
- Disable animations in test with `animations: 'disabled'`
- Check for race conditions in page loading

### Different results between local and CI

- Ensure you're using the same browser version
- Run `npx playwright install` to update browsers
- Font rendering may differ - consider using system fonts or web fonts

## Best Practices

1. **Update baselines intentionally**: Only update when you've made deliberate UI changes
2. **Review diffs carefully**: Always check diff images before approving changes
3. **Keep tests focused**: Test one component or page area at a time
4. **Use meaningful names**: Name screenshots descriptively (e.g., `homepage-hero.png`)
5. **Disable animations**: Use `animations: 'disabled'` for consistent screenshots
6. **Wait for content**: Use `waitForLoadState` to ensure page is fully loaded

## Adding New Tests

To add a new visual regression test:

1. Create or edit a test file in `tests/visual/`
2. Use `toHaveScreenshot()` to capture and compare screenshots
3. Run the test with `--update-snapshots` to create the baseline
4. Commit both the test file and baseline screenshot

Example:
```typescript
import { test, expect } from '@playwright/test';

test('my new page', async ({ page }) => {
  await page.goto('/my-page');
  await page.waitForLoadState('networkidle');
  
  await expect(page).toHaveScreenshot('my-page.png', {
    fullPage: true,
    animations: 'disabled',
  });
});
```

## Resources

- [Playwright Documentation](https://playwright.dev/)
- [Visual Comparisons Guide](https://playwright.dev/docs/test-snapshots)
- [Best Practices](https://playwright.dev/docs/best-practices)
