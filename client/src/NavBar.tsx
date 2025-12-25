import React, { useState } from "react";
import "./css/Nav.css";

import GitHubIcon from "./assets/github.svg?react"
import MathLibLogo from "./assets/mathlib_initiative_logo.svg?react"
import { useNavBar } from "./context/NavBarContext";

export interface NavItem {
  title: React.ReactNode;
  url?: string;
  active?: boolean;
  alt?: string;
  classes?: string;
  blank?: boolean;
}

const NavItemComponent: React.FC<{ item: NavItem }> = ({ item }) => {
  const classes = item.classes ? ` ${item.classes}` : "";

  return (
    <li className={`nav-item-lean${item.active ? " active" : ""}`}>
      {item.url ? (
        <a
          href={item.url}
          className={`bar-link-lean${classes}`}
          aria-label={item.alt || ""}
          target={item.blank ? "_blank" : "_self"}
          rel={item.blank ? "noopener noreferrer" : undefined}
        >
          {item.title}
        </a>
      ) : (
        <button
          className={`bar-link-lean${classes}`}
          aria-label={item.alt || ""}
        >
          {item.title}
        </button>
      )}
    </li>
  );
};

interface NavBarProps {
  logo: React.FC,
  leftItems: NavItem[];
  rightItems: NavItem[];
  menuItems: NavItem[];
  externalLinks: NavItem[];
  classname: string
}

export const NavBar: React.FC<NavBarProps> = ({
  logo: Logo,
  leftItems,
  rightItems,
  menuItems,
  externalLinks,
  classname
}) => {
  const [isNavOpen, setIsNavOpen] = useState(false);
  const [isFroOpen, setIsFroOpen] = useState(false);

  return (
    <header className={`site-header ${classname}`}>
      <nav className="navbar" role="navigation" aria-label="Primary navigation">
        <div className="navbar-container container">
          <Logo />
          <div className="nav-toggle">
            <input
              type="checkbox"
              id="nav-toggle"
              className="nav-toggle-checkbox"
              checked={isNavOpen}
              onChange={(e) => setIsNavOpen(e.target.checked)}
            />
            <label
              htmlFor="nav-toggle"
              className="nav-toggle-label"
              aria-label="Toggle navigation menu"
            >
              ☰
            </label>
          </div>

          <menu className="desktop-menu">
            <ul className="desktop-menu-part">
              {leftItems.map((item, index) => (
                <NavItemComponent key={index} item={item} />
              ))}
              <li>
                <span className="divider" />
              </li>
              {externalLinks.map((item, index) => (
                <NavItemComponent key={index} item={item} />
              ))}
            </ul>
            <ul className="desktop-menu-part">
              {rightItems.map((item, index) => (
                <NavItemComponent key={index} item={item} />
              ))}
            </ul>
          </menu>
        </div>
        <menu className="mobile-nav">
          <ul className="nav-list">
            {leftItems.slice(0, -1).map((item, index) => (
              <NavItemComponent key={index} item={item} />
            ))}
            {externalLinks.slice(0, -1).map((item, index) => (
              <NavItemComponent key={index} item={item} />
            ))}
            <li className="nav-item-lean has-submenu">
              <input
                type="checkbox"
                id="fro-toggle"
                className="fro-toggle-checkbox"
                hidden
                checked={isFroOpen}
                onChange={(e) => setIsFroOpen(e.target.checked)}
              />
              <label
                htmlFor="fro-toggle"
                className="bar-link-lean"
                aria-label="Toggle navigation menu"
              >
                FRO
              </label>
              <ul className="submenu">
                {menuItems.map((item, index) => (
                  <NavItemComponent key={index} item={item} />
                ))}
              </ul>
            </li>
          </ul>
        </menu>
      </nav>
    </header>
  );
};

const LeanLogo: React.FC = () =>
    <a className="nav-logo" href="https://lean-lang.org/">
      <svg
        width="70"
        height="20"
        viewBox="0 0 486 169"
        xmlns="http://www.w3.org/2000/svg"
        stroke="#386EE0"
        fill="transparent"
        strokeWidth="10"
      >
        <path
          d="M206.333 5.67949H105.667M206.333 5.67949L243.25 84.5M206.333 5.67949V84.5M243.25 84.5H317.549M243.25 84.5L279.667 163.321L280.889 163.318L317.549 84.5M206.333 84.5V163.321H5V5M206.333 84.5H105.667M317.549 84.5L353 5.67949M353 5.67949V164M353 5.67949H353.667L480.333 163.454H481V5"
          strokeLinecap="round"
          strokeLinejoin="round"
        ></path>
      </svg>
    </a>

const NavBarLean: React.FC = () => {
  const outItems: NavItem[] = [
    { title: "Playground", url: "https://live.lean-lang.org/", blank: true, active: true },
    {
      title: "Reservoir",
      url: "https://reservoir.lean-lang.org/",
      blank: true,
    },
  ];

  const rightItems: NavItem[] = [
    {
      title: <GitHubIcon style={{fill: "var(--color-text)"}}  />,
      alt: "Github",
      url: "https://github.com/leanprover/lean4",
      blank: true,
    },
  ];

  const leftItems: NavItem[] = [
    { title: "Install", url: "https://lean-lang.org/install" },
    { title: "Learn", url: "https://lean-lang.org/learn" },
    { title: "Community", url: "https://lean-lang.org/community" },
    { title: "Use Cases", url: "https://lean-lang.org/use-cases" },
    { title: "FRO", url: "https://lean-lang.org/fro" },
  ];

  const menuItems = [
    { title: "Home", url: "https://lean-lang.org/fro" },
    { title: "About", url: "https://lean-lang.org/fro/about" },
    { title: "Team", url: "https://lean-lang.org/fro/team" },
    { title: "Roadmap", url: "https://lean-lang.org/fro/roadmap" },
    { title: "Contact", url: "https://lean-lang.org/fro/contact" },

  ];

  return (
    <NavBar
      logo={LeanLogo}
      leftItems={leftItems}
      rightItems={rightItems}
      menuItems={menuItems}
      externalLinks={outItems}
      classname="lean"
    />
  );
};
  
const MathLibIniciativeLogo = () =>
    <MathLibLogo height={40} width={100}/>

const NavBarMathLib: React.FC = () => {
  const outItems: NavItem[] = [
    { title: "Lean", url: "https://lean-lang.org/", blank: true },
    { title: "Mathlib Community", url: "https://leanprover-community.github.io/", blank: true },
    { title: "Playground", url: "https://live.lean-lang.org/?from=lean", blank: true, active: true },
    { title: "Reservoir", url: "https://reservoir.lean-lang.org/", blank: true },
  ];

  const rightItems: NavItem[] = [
    {
      title: <GitHubIcon style={{fill: "var(--color-text)"}}  />,
      alt: "Github",
      url: "https://github.com/leanprover/lean4",
      blank: true,
    }
  ];

  const leftItems: NavItem[] = [
    { title: "About", url: "https://mathlib-initiative.org/about" },
    { title: "Roadmap", url: "https://mathlib-initiative.org/roadmap" },
    { title: "Team", url: "https://mathlib-initiative.org/team" },
    { title: "Careers", url: "https://mathlib-initiative.org/careers" },
    { title: "Support Us", url: "https://mathlib-initiative.org/support" },
    { title: "Contact", url: "https://mathlib-initiative.org/contact" },
  ];

  const menuItems = [
    { title: "Home", url: "https://lean-lang.org/fro" },
    { title: "About", url: "https://lean-lang.org/fro/about" },
    { title: "Team", url: "https://lean-lang.org/fro/team" },
    { title: "Roadmap", url: "https://lean-lang.org/fro/roadmap" },
    { title: "Contact", url: "https://lean-lang.org/fro/contact" },

  ];

  return (
    <NavBar
      logo={MathLibIniciativeLogo}
      leftItems={leftItems}
      rightItems={rightItems}
      menuItems={menuItems}
      externalLinks={outItems}
      classname="mathlib"
    />
  );
};


const NavBarComp: React.FC = () => {
  let navBar = useNavBar()

  return (!navBar.hideNavBar && <>
    {navBar.requiresNavBar === 1 && <NavBarMathLib/>}
    {navBar.requiresNavBar === 2 && <NavBarLean/>}
  </>)

}

export {NavBarLean, NavBarMathLib, NavBarComp};