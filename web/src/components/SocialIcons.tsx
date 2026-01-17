import { SiGithub, SiX } from '@icons-pack/react-simple-icons';

interface SocialLinkProps {
  href: string;
  title: string;
  children: React.ReactNode;
}

function SocialLink({ href, title, children }: SocialLinkProps) {
  return (
    <a
      href={href}
      target="_blank"
      rel="noopener noreferrer"
      title={title}
      aria-label={title}
      className="text-gray-400 hover:text-white transition-colors"
    >
      {children}
    </a>
  );
}

export function SocialIcons() {
  return (
    <div className="flex gap-4">
      <SocialLink
        href="https://twitter.com/cryptoacademy42"
        title="X (Twitter)"
      >
        <SiX size={20} />
      </SocialLink>
      <SocialLink href="https://github.com/cryptographyacademy" title="GitHub">
        <SiGithub size={20} />
      </SocialLink>
    </div>
  );
}

export { SiX, SiGithub };
