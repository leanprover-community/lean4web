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

/** Valid topic names, determined client-side in JoinCollaboration.tsx */
export const zTopic = z.string().regex(/^\w{3,20}$/)

export const zCollabSocketMessage = z.discriminatedUnion('type', [
  z.object({ type: z.literal('subscribe'), topics: z.array(zTopic) }),
  z.object({ type: z.literal('unsubscribe'), topics: z.array(zTopic) }),
  z.object({
    type: z.literal('publish'),
    topic: z.string(),
    data: z.unknown(),
  }),
  z.object({ type: z.literal('ping') }),
])
