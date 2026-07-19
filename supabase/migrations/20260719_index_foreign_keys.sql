-- Foreign-key columns are frequent JOIN/filter targets and should be indexed.
CREATE INDEX IF NOT EXISTS admin_invites_activated_user_id_fkey_idx ON public.admin_invites (activated_user_id);
CREATE INDEX IF NOT EXISTS admin_invites_invited_by_fkey_idx ON public.admin_invites (invited_by);
CREATE INDEX IF NOT EXISTS announcements_sender_id_fkey_idx ON public.announcements (sender_id);
CREATE INDEX IF NOT EXISTS chat_challenges_game_id_fkey_idx ON public.chat_challenges (game_id);
CREATE INDEX IF NOT EXISTS event_messages_bet_id_fkey_idx ON public.event_messages (bet_id);
CREATE INDEX IF NOT EXISTS event_messages_user_id_fkey_idx ON public.event_messages (user_id);
CREATE INDEX IF NOT EXISTS events_created_by_fkey_idx ON public.events (created_by);
CREATE INDEX IF NOT EXISTS game_moves_user_id_fkey_idx ON public.game_moves (user_id);
CREATE INDEX IF NOT EXISTS games_tournament_match_id_fkey_idx ON public.games (tournament_match_id);
CREATE INDEX IF NOT EXISTS games_winner_id_fkey_idx ON public.games (winner_id);
CREATE INDEX IF NOT EXISTS promo_slides_created_by_fkey_idx ON public.promo_slides (created_by);
CREATE INDEX IF NOT EXISTS regional_chat_messages_reply_to_id_fkey_idx ON public.regional_chat_messages (reply_to_id);
CREATE INDEX IF NOT EXISTS regional_chat_messages_user_id_fkey_idx ON public.regional_chat_messages (user_id);
CREATE INDEX IF NOT EXISTS rematch_invites_new_game_id_fkey_idx ON public.rematch_invites (new_game_id);
CREATE INDEX IF NOT EXISTS special_invite_codes_created_by_fkey_idx ON public.special_invite_codes (created_by);
CREATE INDEX IF NOT EXISTS special_invite_codes_used_by_fkey_idx ON public.special_invite_codes (used_by);
CREATE INDEX IF NOT EXISTS spectator_messages_bet_id_fkey_idx ON public.spectator_messages (bet_id);
CREATE INDEX IF NOT EXISTS support_escalations_user_id_fkey_idx ON public.support_escalations (user_id);
CREATE INDEX IF NOT EXISTS tournament_entry_escrows_user_id_fkey_idx ON public.tournament_entry_escrows (user_id);
CREATE INDEX IF NOT EXISTS tournament_matches_game_id_fkey_idx ON public.tournament_matches (game_id);
CREATE INDEX IF NOT EXISTS tournament_matches_loser_id_fkey_idx ON public.tournament_matches (loser_id);
CREATE INDEX IF NOT EXISTS tournament_matches_next_match_id_fkey_idx ON public.tournament_matches (next_match_id);
CREATE INDEX IF NOT EXISTS tournament_matches_player1_id_fkey_idx ON public.tournament_matches (player1_id);
CREATE INDEX IF NOT EXISTS tournament_matches_player2_id_fkey_idx ON public.tournament_matches (player2_id);
CREATE INDEX IF NOT EXISTS tournament_matches_winner_id_fkey_idx ON public.tournament_matches (winner_id);
CREATE INDEX IF NOT EXISTS tournament_participants_registration_id_fkey_idx ON public.tournament_participants (registration_id);
CREATE INDEX IF NOT EXISTS tournament_participants_user_id_fkey_idx ON public.tournament_participants (user_id);
CREATE INDEX IF NOT EXISTS tournament_refund_requests_registration_id_fkey_idx ON public.tournament_refund_requests (registration_id);
CREATE INDEX IF NOT EXISTS tournament_registrations_user_id_fkey_idx ON public.tournament_registrations (user_id);
CREATE INDEX IF NOT EXISTS tournament_registrations_validated_by_fkey_idx ON public.tournament_registrations (validated_by);
CREATE INDEX IF NOT EXISTS tournaments_created_by_fkey_idx ON public.tournaments (created_by);
CREATE INDEX IF NOT EXISTS tournaments_winner_id_fkey_idx ON public.tournaments (winner_id);
CREATE INDEX IF NOT EXISTS xp_history_match_id_fkey_idx ON public.xp_history (match_id);

-- These two indexes are identical; retain the descriptive schema-generated one.
DROP INDEX IF EXISTS public.idx_invite_login_attempts_ident_time;
