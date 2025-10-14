import React, { createContext, useContext, useEffect, useState } from "react";

type NavBarContextType = {
  requiresNavBar: number;
  setRequiresNavBar: React.Dispatch<React.SetStateAction<number>>;
  hideNavBar: boolean;
  setHideNavBar: React.Dispatch<React.SetStateAction<boolean>>;
};

const NavBarContext = createContext<NavBarContextType | undefined>(undefined);

export const NavBarProvider: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const [requiresNavBar, setRequiresNavBar] = useState(0);

  const [hideNavBar, setHideNavBar] = useState<boolean>(() => {
    const stored = localStorage.getItem("hideNavBar");
    return stored ? stored === "true" : false;
  });

  useEffect(() => {
    const params = new URLSearchParams(window.location.search);
    const fromParam = params.get("from");
    if (fromParam === "mathlib") setRequiresNavBar(1);
    else if (fromParam === "lean") setRequiresNavBar(2);
    else setRequiresNavBar(0);

    const hideParam = params.get("hide");
    if (hideParam) setHideNavBar(hideParam === "true");
  }, []);

  useEffect(() => {
    localStorage.setItem("hideNavBar", hideNavBar.toString());
  }, [hideNavBar]);

  return (
    <NavBarContext.Provider
      value={{ requiresNavBar, setRequiresNavBar, hideNavBar, setHideNavBar }}
    >
      {children}
    </NavBarContext.Provider>
  );
};

export const useNavBar = () => {
  const ctx = useContext(NavBarContext);
  if (!ctx) throw new Error("useNavBar must be used inside a NavBarProvider");
  return ctx;
};
