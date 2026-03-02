// ══════════════════════════════════════════════════════════════════
//  AJOUTER CETTE ROUTE dans server.js (après /matchmaking/leave)
//  POST /game/join — Rejoint une partie pré-créée par Mindspille
//  Les deux joueurs arrivent avec le même gameId Supabase
// ══════════════════════════════════════════════════════════════════

app.post('/game/join', requireAuth, (req, res) => {
  const { gameId, username, supabaseId, color } = req.body;
  if (!gameId) return res.status(400).json({ error: 'gameId requis' });

  const userId = req.userId;
  let user = users.get(userId);

  // Créer le user si inconnu (vient de Supabase)
  if (!user) {
    user = { id: userId, username: username || 'Joueur', supabaseId: supabaseId || null };
    users.set(userId, user);
  } else {
    if (username) user.username = username;
    if (supabaseId) user.supabaseId = supabaseId;
  }

  let game = games.get(gameId);

  if (!game) {
    // Premier joueur à arriver — créer la salle avec ce gameId
    game = {
      id: gameId,
      playerWhite: color === 'black' ? null : userId,  // assigne selon la couleur reçue
      playerBlack: color === 'black' ? userId : null,
      board: initialBoard(),
      currentPlayer: 'white',
      status: 'waiting',  // attend le 2ème joueur
      winner: null,
      betAmount: req.body.betAmount || 0,
    };
    games.set(gameId, game);

    console.log(`🏠 Salle créée: ${gameId} — ${user.username} (${color || '?'})`);
    return res.json({ status: 'waiting', gameId, message: 'En attente du 2ème joueur...' });

  } else {
    // 2ème joueur — compléter la partie
    if (game.status === 'playing') {
      // Déjà en cours (reconnexion ?)
      const myColor = game.playerWhite === userId ? 'white' : game.playerBlack === userId ? 'black' : null;
      return res.json({ status: 'ready', gameId, youAre: myColor || color || 'white' });
    }

    // Assigner les couleurs
    if (!game.playerWhite && color !== 'black') {
      game.playerWhite = userId;
    } else if (!game.playerBlack) {
      game.playerBlack = userId;
    } else if (!game.playerWhite) {
      game.playerWhite = userId;
    }

    game.status = 'playing';

    const myColor = game.playerWhite === userId ? 'white' : 'black';
    const opponentId = myColor === 'white' ? game.playerBlack : game.playerWhite;
    const opponentUser = users.get(opponentId);

    // Notifier les deux joueurs via Socket.io que la partie commence
    const wUser = users.get(game.playerWhite);
    const bUser = users.get(game.playerBlack);
    const host = `${req.protocol}://${req.get('host')}`;

    const basePayload = {
      gameId,
      betAmount: game.betAmount,
      white: { userId: game.playerWhite, username: wUser?.username, supabaseId: wUser?.supabaseId },
      black: { userId: game.playerBlack, username: bUser?.username, supabaseId: bUser?.supabaseId },
    };

    emitToUser(game.playerWhite, 'match:found', {
      ...basePayload, youAre: 'white',
      gameUrl: `${host}/game?gameId=${gameId}&player=${game.playerWhite}`
    });
    emitToUser(game.playerBlack, 'match:found', {
      ...basePayload, youAre: 'black',
      gameUrl: `${host}/game?gameId=${gameId}&player=${game.playerBlack}`
    });

    console.log(`✅ Partie démarrée: ${wUser?.username}(⬜) vs ${bUser?.username}(⬛) — ${gameId}`);

    return res.json({
      status: 'ready',
      gameId,
      youAre: myColor,
      opponent: opponentUser?.username,
    });
  }
});
