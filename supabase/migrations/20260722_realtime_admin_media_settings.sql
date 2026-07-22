-- Broadcast administrator media decisions to every connected client.
-- platform_settings was already in the publication; add the dependent media
-- tables so slide/track edits are reflected without a reload. Default cards
-- live in platform_settings.featured_default_slides, not a separate table.
DO $$
DECLARE
  table_name text;
BEGIN
  FOREACH table_name IN ARRAY ARRAY['promo_slides', 'music_tracks']
  LOOP
    IF NOT EXISTS (
      SELECT 1
      FROM pg_publication_tables
      WHERE pubname = 'supabase_realtime'
        AND schemaname = 'public'
        AND tablename = table_name
    ) THEN
      EXECUTE format('ALTER PUBLICATION supabase_realtime ADD TABLE public.%I', table_name);
    END IF;
  END LOOP;
END;
$$;
