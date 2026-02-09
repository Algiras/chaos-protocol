import * as React from "react";
import { Slot } from "@radix-ui/react-slot";
import { cva, type VariantProps } from "class-variance-authority";
import { cn } from "@/lib/utils";
import { useFractalRipple } from "@/components/chaos/effects/FractalRipple";

const buttonVariants = cva(
  "inline-flex items-center justify-center whitespace-nowrap rounded-md text-sm font-medium ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50",
  {
    variants: {
      variant: {
        default: "bg-primary text-primary-foreground hover:bg-primary/90",
        destructive:
          "bg-destructive text-destructive-foreground hover:bg-destructive/90",
        outline:
          "border border-input bg-background hover:bg-accent hover:text-accent-foreground",
        secondary:
          "bg-secondary text-secondary-foreground hover:bg-secondary/80",
        ghost: "hover:bg-accent hover:text-accent-foreground",
        link: "text-primary underline-offset-4 hover:underline",
        chaos:
          "relative overflow-hidden bg-gradient-to-r from-chaos-primary-600 via-chaos-accent-purple to-chaos-primary-500 text-white hover:shadow-lg hover:scale-[1.02] transition-all duration-500",
      },
      size: {
        default: "h-10 px-4 py-2",
        sm: "h-9 rounded-md px-3",
        lg: "h-11 rounded-md px-8",
        icon: "h-10 w-10",
      },
    },
    defaultVariants: {
      variant: "default",
      size: "default",
    },
  }
);

export interface ButtonProps
  extends React.ButtonHTMLAttributes<HTMLButtonElement>,
    VariantProps<typeof buttonVariants> {
  asChild?: boolean;
  /** Enable fractal ripple effect on click (enabled by default for chaos variant) */
  enableRipple?: boolean;
}

const Button = React.forwardRef<HTMLButtonElement, ButtonProps>(
  ({ className, variant, size, asChild = false, enableRipple, onClick, ...props }, ref) => {
    const Comp = asChild ? Slot : "button";
    const { ripples, addRipple } = useFractalRipple();
    const buttonRef = React.useRef<HTMLButtonElement>(null);

    // Enable ripple by default for chaos variant
    const shouldEnableRipple = enableRipple ?? variant === "chaos";

    const handleClick = (e: React.MouseEvent<HTMLButtonElement>) => {
      if (shouldEnableRipple && buttonRef.current) {
        const rect = buttonRef.current.getBoundingClientRect();
        const x = e.clientX - rect.left;
        const y = e.clientY - rect.top;
        addRipple(x, y);
      }
      onClick?.(e);
    };

    React.useImperativeHandle(ref, () => buttonRef.current!);

    return (
      <Comp
        className={cn(buttonVariants({ variant, size, className }))}
        ref={buttonRef}
        onClick={handleClick}
        {...props}
      >
        {props.children}
        {shouldEnableRipple && ripples}
      </Comp>
    );
  }
);
Button.displayName = "Button";

export { Button, buttonVariants };
