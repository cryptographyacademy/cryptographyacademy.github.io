import { test, expect } from '@playwright/test';

/**
 * Visual regression tests for critical pages
 * 
 * These tests capture screenshots of each page at different viewport sizes
 * and compare them against baseline images to detect visual regressions.
 */

// Helper function to wait for page to be fully loaded
async function waitForPageLoad(page) {
  await page.waitForLoadState('networkidle');
  await page.waitForLoadState('domcontentloaded');
  // Give animations and fonts time to settle
  await page.waitForTimeout(500);
}

test.describe('Homepage Visual Tests', () => {
  test('should match baseline screenshot', async ({ page }) => {
    await page.goto('/');
    await waitForPageLoad(page);
    
    // Take full page screenshot
    await expect(page).toHaveScreenshot('homepage.png', {
      fullPage: true,
      animations: 'disabled',
    });
  });
  
  test('should match hero section', async ({ page }) => {
    await page.goto('/');
    await waitForPageLoad(page);
    
    // Screenshot just the hero section
    const hero = page.locator('section').first();
    await expect(hero).toHaveScreenshot('homepage-hero.png', {
      animations: 'disabled',
    });
  });
  
  test('should match feature cards', async ({ page }) => {
    await page.goto('/');
    await waitForPageLoad(page);
    
    // Screenshot the feature cards grid
    const features = page.locator('section').nth(1);
    await expect(features).toHaveScreenshot('homepage-features.png', {
      animations: 'disabled',
    });
  });
});

test.describe('Setup Page Visual Tests', () => {
  test('should match baseline screenshot', async ({ page }) => {
    await page.goto('/setup');
    await waitForPageLoad(page);
    
    await expect(page).toHaveScreenshot('setup-page.png', {
      fullPage: true,
      animations: 'disabled',
    });
  });
});

test.describe('Foundations Page Visual Tests', () => {
  test('should match baseline screenshot', async ({ page }) => {
    await page.goto('/foundations');
    await waitForPageLoad(page);
    
    await expect(page).toHaveScreenshot('foundations-page.png', {
      fullPage: true,
      animations: 'disabled',
    });
  });
});

test.describe('Primitives Page Visual Tests', () => {
  test('should match baseline screenshot', async ({ page }) => {
    await page.goto('/primitives');
    await waitForPageLoad(page);
    
    await expect(page).toHaveScreenshot('primitives-page.png', {
      fullPage: true,
      animations: 'disabled',
    });
  });
});

test.describe('Proofs Page Visual Tests', () => {
  test('should match baseline screenshot', async ({ page }) => {
    await page.goto('/proofs');
    await waitForPageLoad(page);
    
    await expect(page).toHaveScreenshot('proofs-page.png', {
      fullPage: true,
      animations: 'disabled',
    });
  });
});

test.describe('About Page Visual Tests', () => {
  test('should match baseline screenshot', async ({ page }) => {
    await page.goto('/about');
    await waitForPageLoad(page);
    
    await expect(page).toHaveScreenshot('about-page.png', {
      fullPage: true,
      animations: 'disabled',
    });
  });
});

test.describe('Navigation Component Visual Tests', () => {
  test('should match navigation on desktop', async ({ page }) => {
    await page.goto('/');
    await waitForPageLoad(page);
    
    const nav = page.locator('nav').first();
    await expect(nav).toHaveScreenshot('navigation-desktop.png', {
      animations: 'disabled',
    });
  });
  
  test('should match footer', async ({ page }) => {
    await page.goto('/');
    await waitForPageLoad(page);
    
    const footer = page.locator('footer');
    await expect(footer).toHaveScreenshot('footer.png', {
      animations: 'disabled',
    });
  });
});
