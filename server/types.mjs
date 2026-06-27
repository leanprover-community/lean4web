import { z } from 'zod'

export const zLeanWebExample = z.object({
  file: z.string(),
  name: z.string(),
})

export const zLeanWebProjectConfig = z.object({
  name: z.string(),
  hidden: z.boolean().optional(),
  default: z.boolean().optional(),
  sortOrder: z.number().min(0).optional(),
  examples: z.array(zLeanWebExample).optional(),
})
