# Shiny simulation: survival + public goods game
# Phase 1 = public good game, Phase 2 = stockpile vs bonus,
# Crisis = survive on the stockpile,
# Phase 4a/4b = post-crisis public good and stockpile rounds,
# Overall outcomes = whole-game figures, group indicators, final payoffs, CSV download
# Run with: shiny::runApp("pgg_normal_rounds")
# Needs: shiny, ggplot2

library(shiny)
library(ggplot2)

# ---- Game logic -------------------------------------------------------------
# Normal rounds (before and after the crisis), per player and round:
#   Phase 1 (public good)
#     1. wallet: the endowment E_i arrives every round (wallet resets), or only in the
#        first round of each block of normal rounds (wallet carries over)
#     2. pay the tax (flat points) into the public good (capped at the wallet)
#     3. pay the survival cost out of what is left (capped at the wallet)
#     4. contribute a share (voluntary rate) of the leftover to the public good
#     5. keep the rest, and receive an equal share of the multiplied pool
#        (split among the players still in the game)
#     Spendable income = kept + pool share. With a one-off endowment, kept money stays
#     in the wallet until the last round of the block and only the pool share is spendable
#     before that.
#   Phase 2 (stockpile)
#     spendable income is split by the stockpile rate: the stockpile part is added
#     to the stock (no decay, 1:1), the rest is banked as bonus (1:1).
#
# Missing the survival cost is punished by one of:
#   flat points per round | points per unpaid unit |
#   no bonus from that round on (stock can still be built) |
#   removal from the game from that round on (no share, no bonus, stock is lost)
#
# Crisis rounds, per player and round (no endowment, the tax public good is offline):
#   1. survival cost is paid from the stock (capped at what they have)
#   2. a share (crisis contribution rate) of the stock left after survival goes to the
#      stockpile public good
#   3. the pool is multiplied and shared equally among players still in the game, and
#      the share is added to the stock before the next crisis round
#
# Post-crisis rounds: normal rounds again (Phase 4a and 4b), starting from each player's
# stock and status at the end of the crisis. The public good multiplier is one of:
#   constant | rising in steps up to a maximum | low until the group's cumulative
#   voluntary contributions reach a threshold, then the maximum from the next round on
#
# Final payoff = bonus (before and after the crisis) - crisis penalties
#                + cash-out rate * final stock (no cash-out if bonus was forfeited or removed)

clamp01 <- function(x) pmin(pmax(x, 0), 1)

player_factor <- function(n) {
  lv <- paste0("P", seq_len(n))
  factor(lv, levels = lv)
}

penalty_for <- function(unpaid, penalty, per_unit) {
  ifelse(unpaid > 0, if (per_unit) penalty * unpaid else penalty, 0)
}

# Points penalty for the two points-based rules, zero for the other rules
points_penalty <- function(unpaid, penalty, penalty_type) {
  if (penalty_type == "flat")          penalty_for(unpaid, penalty, FALSE)
  else if (penalty_type == "per_unit") penalty_for(unpaid, penalty, TRUE)
  else                                 rep(0, length(unpaid))
}

# Multiplier per round when rebuilding in steps
mult_schedule <- function(rounds, start, step, every, max_m) {
  pmin(max_m, start + step * ((seq_len(rounds) - 1) %/% max(1, every)))
}

# thr = NULL uses `mult` (one value per round). Otherwise thr = list(low, high, amount):
# the multiplier is `low` until the group's cumulative voluntary contributions
# (from earlier rounds) reach `amount`, and `high` afterwards.
simulate_normal <- function(E, tax, S, penalty, penalty_type, mult, rounds,
                            c_rates, s_rates, noise_sd, stock0 = 0, round_offset = 0,
                            thr = NULL, endow_mode = "each_round",
                            removed0 = NULL, nobonus0 = NULL) {
  n       <- length(E)
  removed <- if (is.null(removed0)) rep(FALSE, n) else removed0
  nobonus <- if (is.null(nobonus0)) rep(FALSE, n) else nobonus0
  stock   <- rep_len(stock0, n)
  wallet  <- rep(0, n)
  cum_c   <- 0
  out     <- vector("list", rounds)
  
  for (r in seq_len(rounds)) {
    m <- if (!is.null(thr)) {
      if (cum_c >= thr$amount) thr$high else thr$low
    } else rep_len(mult, rounds)[r]
    
    stock_start_i <- stock
    active   <- !removed
    fresh    <- endow_mode == "each_round" || r == 1
    endow_in <- if (fresh) E * active else rep(0, n)
    W        <- if (fresh) endow_in else wallet
    
    # Phase 1
    tax_paid  <- pmin(tax, W);  W <- W - tax_paid
    surv_paid <- pmin(S, W)
    unpaid    <- (S - surv_paid) * active
    W         <- W - surv_paid
    failed    <- active & unpaid > 0
    disc      <- W
    contrib   <- disc * clamp01(c_rates + rnorm(n, 0, noise_sd))
    kept      <- disc - contrib
    
    removed_now <- if (penalty_type == "removed") removed | failed else removed
    recv        <- !removed_now
    pool        <- sum(tax_paid) + sum(contrib)
    share       <- if (sum(recv) > 0) m * pool / sum(recv) else 0
    share_i     <- share * recv
    cum_c       <- cum_c + sum(contrib)
    
    release   <- endow_mode == "each_round" || r == rounds
    spendable <- (if (release) kept else 0) + share_i
    spendable <- spendable * recv
    wallet    <- if (release) rep(0, n) else kept * recv
    
    # Phase 2
    to_stock    <- spendable * clamp01(s_rates + rnorm(n, 0, noise_sd))
    nobonus_now <- nobonus | (failed & penalty_type == "no_bonus")
    bonus_gross <- ifelse(nobonus_now, 0, spendable - to_stock)
    pen         <- points_penalty(unpaid, penalty, penalty_type)
    stock       <- (stock + to_stock) * recv     # removed players lose their stock
    
    out[[r]] <- data.frame(
      round = r + round_offset, player = player_factor(n), active = active,
      multiplier = m, endowment = endow_in, tax_paid = tax_paid,
      survival_paid = surv_paid, unpaid = unpaid, discretionary = disc,
      contribution = contrib, kept = kept, pool_share = share_i, spendable = spendable,
      to_stock = to_stock, penalty = pen, bonus = bonus_gross - pen,
      cum_group_contrib = cum_c, wallet_end = wallet, stock = stock,
      stock_start = stock_start_i, bonus_forfeited = nobonus_now, removed_end = removed_now
    )
    removed <- removed_now
    nobonus <- nobonus_now
  }
  res <- do.call(rbind, out)
  res$cum_bonus <- ave(res$bonus, res$player, FUN = cumsum)
  res
}

simulate_crisis <- function(stock0, S, penalty, penalty_type, mult, rounds,
                            k_rates, noise_sd, removed0 = NULL, nobonus0 = NULL) {
  n       <- length(stock0)
  removed <- if (is.null(removed0)) rep(FALSE, n) else removed0
  nobonus <- if (is.null(nobonus0)) rep(FALSE, n) else nobonus0
  stock   <- stock0
  out     <- vector("list", rounds)
  
  for (r in seq_len(rounds)) {
    active      <- !removed
    surv_paid   <- pmin(S, stock)
    unpaid      <- (S - surv_paid) * active
    failed      <- active & unpaid > 0
    stock_after <- stock - surv_paid
    contrib     <- stock_after * clamp01(k_rates + rnorm(n, 0, noise_sd))
    
    removed_now <- if (penalty_type == "removed") removed | failed else removed
    recv        <- !removed_now
    share       <- if (sum(recv) > 0) mult * sum(contrib) / sum(recv) else 0
    share_i     <- share * recv
    stock_end   <- (stock_after - contrib + share_i) * recv
    nobonus_now <- nobonus | (failed & penalty_type == "no_bonus")
    
    out[[r]] <- data.frame(
      round = r, player = player_factor(n), active = active, stock_start = stock,
      survival_paid = surv_paid, unpaid = unpaid, stock_after = stock_after,
      contribution = contrib, pool_share = share_i,
      penalty = points_penalty(unpaid, penalty, penalty_type),
      stock_end = stock_end, bonus_forfeited = nobonus_now, removed_end = removed_now
    )
    stock   <- stock_end
    removed <- removed_now
    nobonus <- nobonus_now
  }
  do.call(rbind, out)
}

# Puts both crisis modes into one common shape: round, player, active, stock_start,
# survival_paid, unpaid, contribution, pool_share, stock_end, penalty, bonus,
# bonus_forfeited, removed_end, plus endowment/tax_paid/kept/spendable/to_stock/
# discretionary/available/multiplier (NA in offline mode, where the public good is off).
unify_crisis <- function(mode, raw, mult_offline) {
  if (mode == "offline") {
    data.frame(
      round = raw$round, player = raw$player, active = raw$active,
      multiplier = mult_offline, endowment = NA_real_, tax_paid = NA_real_,
      stock_start = raw$stock_start, survival_paid = raw$survival_paid, unpaid = raw$unpaid,
      discretionary = NA_real_, available = raw$stock_after,
      contribution = raw$contribution, kept = NA_real_, pool_share = raw$pool_share,
      spendable = NA_real_, to_stock = NA_real_, penalty = raw$penalty,
      bonus = -raw$penalty, stock_end = raw$stock_end,
      bonus_forfeited = raw$bonus_forfeited, removed_end = raw$removed_end
    )
  } else {
    data.frame(
      round = raw$round, player = raw$player, active = raw$active,
      multiplier = raw$multiplier, endowment = raw$endowment, tax_paid = raw$tax_paid,
      stock_start = raw$stock_start, survival_paid = raw$survival_paid, unpaid = raw$unpaid,
      discretionary = raw$discretionary, available = raw$discretionary,
      contribution = raw$contribution, kept = raw$kept, pool_share = raw$pool_share,
      spendable = raw$spendable, to_stock = raw$to_stock, penalty = raw$penalty,
      bonus = raw$bonus, stock_end = raw$stock,
      bonus_forfeited = raw$bonus_forfeited, removed_end = raw$removed_end
    )
  }
}

# One line per player, x = round
line_plot <- function(d, y, title, ylab, xlab = "Round") {
  ggplot(d, aes(round, .data[[y]], colour = player)) +
    geom_line(linewidth = 1) + geom_point() +
    scale_x_continuous(breaks = unique(d$round)) +
    labs(title = title, x = xlab, y = ylab, colour = NULL) +
    theme_minimal(base_size = 13)
}

# Tile chart: did each player meet the survival cost in each round?
survival_plot <- function(d, title, xlab = "Round") {
  u <- if ("unpaid" %in% names(d)) d$unpaid else d$survival_unpaid
  d$status <- factor(ifelse(!d$active, "Removed", ifelse(u > 0, "Missed", "Met")),
                     levels = c("Met", "Missed", "Removed"))
  d$label <- c(Met = "Yes", Missed = "No", Removed = "Out")[as.character(d$status)]
  ggplot(d, aes(round, player, fill = status)) +
    geom_tile(colour = "white", linewidth = 0.8) +
    geom_text(aes(label = label), colour = "white", size = 3.3) +
    scale_fill_manual(values = c(Met = "#3a9d5d", Missed = "#d64545", Removed = "grey60"),
                      drop = FALSE, name = "Survival cost met") +
    scale_x_continuous(breaks = unique(d$round)) +
    scale_y_discrete(limits = rev(levels(d$player))) +
    labs(title = title, x = xlab, y = NULL) +
    theme_minimal(base_size = 13) +
    theme(panel.grid = element_blank())
}

# Dashed lines marking where the crisis starts (and ends, if later rounds are shown)
crisis_layers <- function(R, K, has_post, ymax, label = "crisis") {
  list(
    geom_vline(xintercept = c(R + 0.5, if (has_post) R + K + 0.5),
               linetype = "dashed", colour = "grey50"),
    annotate("text", x = R + 0.6, y = ymax, label = label,
             hjust = 0, vjust = 1, colour = "grey40", size = 4)
  )
}

# Sum a column per player over a subset of rows (zeros when the subset is empty)
sum_by_player <- function(d, col, players) {
  out <- setNames(rep(0, length(players)), players)
  if (nrow(d) > 0) {
    s <- tapply(d[[col]], d$player, sum)
    out[names(s)] <- s
  }
  out
}

# ---- Game log: one HTML table per round, in chronological order ------------
fmt_cell <- function(x) {
  if (is.character(x) || is.factor(x)) return(as.character(x))
  ifelse(is.na(x), "", formatC(x, format = "f", digits = 2))
}

df_html_table <- function(df) {
  header <- tags$tr(lapply(names(df), tags$th))
  rows <- lapply(seq_len(nrow(df)), function(i) {
    tags$tr(lapply(names(df), function(nm) tags$td(fmt_cell(df[[nm]][i]))))
  })
  tags$table(class = "table table-condensed table-striped",
             style = "width:auto; margin-bottom: 24px;",
             tags$thead(header), tags$tbody(rows))
}

status_label <- function(active, removed, bonus_forfeited) {
  ifelse(removed & active, "Removed this round",
         ifelse(removed & !active, "Out",
                ifelse(bonus_forfeited, "No bonus", "Active")))
}

survival_label <- function(active, unpaid) {
  ifelse(!active, "\u2014", ifelse(unpaid > 0, "No", "Yes"))
}

build_round_block <- function(d, r, R, K) {
  x <- d[d$round == r, ]
  phase <- x$phase[1]
  surv  <- survival_label(x$active, x$survival_unpaid)
  stat  <- status_label(x$active, x$removed, x$bonus_forfeited)
  
  if (phase == "crisis") {
    active_pg <- !all(is.na(x$endowment))
    if (active_pg) {
      header_txt <- paste0("Round ", r, " \u2014 Crisis round ", r - R, " of ", K, " (public good active, degraded)")
      tbl <- data.frame(
        Player = as.character(x$player), Endowment = x$endowment, `Tax paid` = x$tax_paid,
        `Survival paid` = x$survival_paid, `Survival met?` = surv, Contribution = x$contribution,
        Kept = x$kept, `Pool share` = x$pool_share, Spendable = x$spendable,
        `To stockpile` = x$to_stock, `Bonus (net)` = x$earnings, Stock = x$stock_end,
        Status = stat, check.names = FALSE
      )
    } else {
      header_txt <- paste0("Round ", r, " \u2014 Crisis round ", r - R, " of ", K, " (public good offline)")
      tbl <- data.frame(
        Player = as.character(x$player), `Stock at start` = x$stock_start,
        `Survival paid` = x$survival_paid, `Survival met?` = surv,
        Contribution = x$contribution, `Pool share` = x$pool_share,
        `Stock at end` = x$stock_end, Status = stat, check.names = FALSE
      )
    }
  } else {
    label <- if (phase == "normal_before_crisis") "Normal round (before crisis)" else "Normal round (after crisis)"
    header_txt <- paste0("Round ", r, " \u2014 ", label)
    tbl <- data.frame(
      Player = as.character(x$player), Endowment = x$endowment,
      `Tax paid` = x$tax_paid, `Survival paid` = x$survival_paid,
      `Survival met?` = surv, Contribution = x$contribution, Kept = x$kept,
      `Pool share` = x$pool_share, Spendable = x$spendable,
      `To stockpile` = x$to_stock, `Bonus (net)` = x$earnings,
      Stock = x$stock_end, Status = stat, check.names = FALSE
    )
  }
  tagList(tags$h4(header_txt), df_html_table(tbl))
}

# ---- UI ---------------------------------------------------------------------
ui <- fluidPage(
  titlePanel("Public goods game with survival costs and a crisis"),
  sidebarLayout(
    sidebarPanel(
      width = 3,
      h4("Game settings"),
      radioButtons(
        "endow_mode", "Endowment",
        choices = c("Every round" = "each_round",
                    "Once, at the start of each block of normal rounds" = "once")
      ),
      helpText("With a one-off endowment, tax, survival cost and contributions all come out of one wallet that carries over. Unspent money is released as spendable income in the block's last round; before that only the pool share is spendable."),
      numericInput("tax", "Tax per player per round (points, into the public good)",
                   value = 2, min = 0, step = 0.5),
      numericInput("S", "Survival cost per round (normal rounds)", value = 4, min = 0, step = 1),
      numericInput("mult", "Public good multiplier (normal rounds)", value = 2, min = 0, step = 0.1),
      radioButtons(
        "penalty_type", "Penalty for not meeting the survival cost",
        choices = c("Points, flat per round" = "flat",
                    "Points, per unpaid unit" = "per_unit",
                    "No bonus for the rest of the game" = "no_bonus",
                    "Removed from the game" = "removed")
      ),
      conditionalPanel(
        "input.penalty_type == 'flat' || input.penalty_type == 'per_unit'",
        numericInput("penalty", "Penalty points", value = 12, min = 0, step = 1)
      ),
      conditionalPanel(
        "input.penalty_type == 'no_bonus'",
        helpText("From the round they miss survival, the player banks no more bonus and gets no stock cash-out. Bonus already banked is kept, and they can still build and use a stockpile.")
      ),
      conditionalPanel(
        "input.penalty_type == 'removed'",
        helpText("From the round they miss survival, the player is out: no pool share, no bonus, no further rounds, and their stock is lost. Bonus already banked is kept.")
      ),
      numericInput("rounds", "Number of normal rounds (before the crisis)", value = 6, min = 1, max = 50, step = 1),
      numericInput("n", "Number of players", value = 4, min = 2, max = 10, step = 1),
      hr(),
      h4("Behavioral noise (optional)"),
      sliderInput("noise", "Round-to-round noise in rates (SD)",
                  min = 0, max = 0.5, value = 0, step = 0.05),
      numericInput("seed", "Random seed", value = 1, step = 1),
      hr(),
      h4("Data"),
      downloadButton("download_rounds", "Download per-round data (CSV)"),
      helpText("One row per player per round for the whole game. Crisis rows use the stockpile pool; columns that do not apply are empty.")
    ),
    mainPanel(
      width = 9,
      tabsetPanel(
        id = "tabs",
        
        # ---- Phase 1
        tabPanel(
          "Phase 1: Public good",
          br(),
          h4("Players"),
          uiOutput("phase1_inputs"),
          h4("Round setup per player"),
          tableOutput("setup"),
          fluidRow(
            column(6, plotOutput("plot_contrib", height = 280)),
            column(6, plotOutput("plot_spendable", height = 280))
          ),
          plotOutput("plot_survival1", height = "auto"),
          h4("Phase 1 totals per player"),
          tableOutput("totals1"),
          h4("Round-by-round results"),
          tableOutput("detail1")
        ),
        
        # ---- Phase 2
        tabPanel(
          "Phase 2: Stockpile",
          br(),
          h4("Stockpile rate per player"),
          p("Share of each round's spendable income (kept income plus public good share) that goes into the stockpile. The rest is banked as bonus."),
          uiOutput("phase2_inputs"),
          fluidRow(
            column(6, plotOutput("plot_stock", height = 280)),
            column(6, plotOutput("plot_bonus", height = 280))
          ),
          h4("Phase 2 totals per player"),
          tableOutput("totals2"),
          h4("Round-by-round results"),
          tableOutput("detail2")
        ),
        
        # ---- Crisis
        tabPanel(
          "Crisis rounds",
          br(),
          h4("Crisis settings"),
          fluidRow(
            column(4, numericInput("crisis_rounds", "Number of crisis rounds",
                                   value = 3, min = 1, max = 30, step = 1)),
            column(4, numericInput("S_crisis", "Survival cost per crisis round",
                                   value = 4, min = 0, step = 1)),
            column(4, radioButtons("crisis_pg_mode", "Public good during the crisis",
                                   choices = c("Offline (survive on the stockpile)" = "offline",
                                               "Active but degraded" = "active")))
          ),
          conditionalPanel(
            "input.crisis_pg_mode == 'offline'",
            fluidRow(column(4, numericInput("mult_stock", "Stockpile public good multiplier",
                                            value = 1, min = 0, step = 0.1))),
            h4("Contribution to the stockpile public good"),
            p("Share of the stock left after survival is paid that each player contributes. The pool is shared equally before the next crisis round."),
            uiOutput("crisis_inputs")
          ),
          conditionalPanel(
            "input.crisis_pg_mode == 'active'",
            fluidRow(
              column(4, numericInput("crisis_tax", "Tax per player per crisis round (points, into the public good)",
                                     value = 1, min = 0, step = 0.5)),
              column(4, numericInput("crisis_mult", "Crisis public good multiplier",
                                     value = 1, min = 0, step = 0.1))
            ),
            helpText("The crisis endowment, tax and multiplier are separate settings from the normal rounds, so you can make them worse (a very low endowment, a poor multiplier) without changing the normal-round game."),
            h4("Players during the crisis"),
            p("Endowment and voluntary contribution rate to the (degraded) public good, plus how much of that round's spendable income each player sends to the stockpile."),
            uiOutput("crisis_active_pg_inputs"),
            uiOutput("crisis_active_stock_inputs")
          ),
          h4("Crisis start per player"),
          tableOutput("crisis_setup"),
          fluidRow(
            column(6, plotOutput("plot_stock_crisis", height = 280)),
            column(6, plotOutput("plot_crisis_contrib", height = 280))
          ),
          plotOutput("plot_survival_crisis", height = "auto"),
          h4("Crisis totals per player"),
          tableOutput("crisis_totals"),
          h4("Crisis round-by-round results"),
          tableOutput("crisis_detail")
        ),
        
        # ---- Phase 4a
        tabPanel(
          "Phase 4a: Post-crisis public good",
          br(),
          h4("Post-crisis settings"),
          fluidRow(
            column(4, numericInput("rounds_post", "Normal rounds after the crisis (0 = none)",
                                   value = 6, min = 0, max = 50, step = 1)),
            column(4, numericInput("tax_post", "Tax per player per round (points)",
                                   value = 2, min = 0, step = 0.5)),
            column(4, numericInput("S_post", "Survival cost per round",
                                   value = 4, min = 0, step = 1))
          ),
          radioButtons(
            "rebuild_mode", "Public good multiplier after the crisis",
            choices = c("Constant" = "constant",
                        "Rebuild in steps" = "steps",
                        "Rebuild at a contribution threshold" = "threshold"),
            inline = TRUE
          ),
          conditionalPanel(
            "input.rebuild_mode == 'constant'",
            fluidRow(column(4, numericInput("mult_post", "Multiplier", value = 2, min = 0, step = 0.1)))
          ),
          conditionalPanel(
            "input.rebuild_mode == 'steps'",
            fluidRow(
              column(3, numericInput("mult_start", "Starting multiplier", value = 1, min = 0, step = 0.1)),
              column(3, numericInput("mult_step", "Increase per step", value = 0.25, step = 0.05)),
              column(3, numericInput("mult_every", "Rounds per step", value = 1, min = 1, step = 1)),
              column(3, numericInput("mult_max", "Maximum multiplier", value = 2, min = 0, step = 0.1))
            )
          ),
          conditionalPanel(
            "input.rebuild_mode == 'threshold'",
            fluidRow(
              column(4, numericInput("thr_low", "Multiplier while rebuilding", value = 1, min = 0, step = 0.1)),
              column(4, numericInput("thr_amount", "Group contribution threshold (cumulative voluntary points)",
                                     value = 30, min = 0, step = 1)),
              column(4, numericInput("thr_high", "Maximum multiplier once reached", value = 2, min = 0, step = 0.1))
            ),
            helpText("Voluntary contributions by all players are summed over the post-crisis rounds. Once the total reaches the threshold, the multiplier switches to the maximum from the next round on and stays there. Tax does not count.")
          ),
          h4("Players"),
          uiOutput("post_pg_inputs"),
          textOutput("post_status"),
          h4("Round setup per player"),
          tableOutput("post_setup"),
          fluidRow(
            column(6, plotOutput("plot_mult", height = 260)),
            column(6, plotOutput("plot_post_cumgroup", height = 260))
          ),
          fluidRow(
            column(6, plotOutput("plot_post_contrib", height = 260)),
            column(6, plotOutput("plot_post_spendable", height = 260))
          ),
          plotOutput("plot_survival_post", height = "auto"),
          h4("Phase 4a totals per player"),
          tableOutput("post_totals1"),
          h4("Round-by-round results"),
          tableOutput("post_detail1")
        ),
        
        # ---- Phase 4b
        tabPanel(
          "Phase 4b: Post-crisis stockpile",
          br(),
          h4("Stockpile rate per player"),
          p("Share of each post-crisis round's spendable income that goes into the stockpile. The rest is banked as bonus."),
          uiOutput("post_stock_inputs"),
          fluidRow(column(4, numericInput("cashout", "Final stock cash-out rate",
                                          value = 0, min = 0, max = 1, step = 0.05))),
          fluidRow(
            column(6, plotOutput("plot_post_stock", height = 280)),
            column(6, plotOutput("plot_post_bonus", height = 280))
          ),
          h4("Phase 4b totals per player"),
          tableOutput("post_totals2"),
          h4("Round-by-round results"),
          tableOutput("post_detail2")
        ),
        
        # ---- Overall
        tabPanel(
          "Overall outcomes",
          br(),
          fluidRow(
            column(6, plotOutput("plot_stock_all", height = 300)),
            column(6, plotOutput("plot_earnings_all", height = 300))
          ),
          fluidRow(
            column(6, plotOutput("plot_indicators", height = 300)),
            column(6, plotOutput("plot_survival_all", height = "auto"))
          ),
          h4("Group indicators"),
          tableOutput("indicators"),
          h4("Final payoff per player (whole game)"),
          tableOutput("payoff")
        ),
        
        # ---- Game log
        tabPanel(
          "Game log",
          br(),
          p("Every player's decisions and outcomes, round by round, in the order they happened. Each round is headed by its phase."),
          uiOutput("game_log")
        )
      )
    )
  )
)

# ---- Server -----------------------------------------------------------------
server <- function(input, output, session) {
  
  default_E  <- 12
  default_Ec <- 4
  default_c <- c(1, 0.5, 0.25, 0)
  default_s <- c(0.5, 1, 0.25, 0)
  default_k <- c(0.5, 0, 1, 0.25)
  
  # Per-player inputs; keep existing values when the player count changes
  keep <- function(id, default) {
    cur <- isolate(input[[id]])
    if (is.null(cur)) default else cur
  }
  
  output$phase1_inputs <- renderUI({
    n <- req(input$n)
    lapply(seq_len(n), function(i) {
      fluidRow(
        column(4, numericInput(paste0("E_", i), paste0("Player ", i, ": endowment"),
                               value = keep(paste0("E_", i), default_E), min = 0, step = 1)),
        column(8, sliderInput(paste0("c_", i), "Voluntary contribution rate",
                              min = 0, max = 1, step = 0.05,
                              value = keep(paste0("c_", i), rep_len(default_c, i)[i])))
      )
    })
  })
  
  output$phase2_inputs <- renderUI({
    n <- req(input$n)
    lapply(seq_len(n), function(i) {
      sliderInput(paste0("s_", i), paste0("Player ", i, ": stockpile rate"),
                  min = 0, max = 1, step = 0.05,
                  value = keep(paste0("s_", i), rep_len(default_s, i)[i]))
    })
  })
  
  output$crisis_inputs <- renderUI({
    n <- req(input$n)
    lapply(seq_len(n), function(i) {
      sliderInput(paste0("k_", i), paste0("Player ", i, ": crisis contribution rate"),
                  min = 0, max = 1, step = 0.05,
                  value = keep(paste0("k_", i), rep_len(default_k, i)[i]))
    })
  })
  
  output$crisis_active_pg_inputs <- renderUI({
    n <- req(input$n)
    lapply(seq_len(n), function(i) {
      fluidRow(
        column(4, numericInput(paste0("Ec_", i), paste0("Player ", i, ": crisis endowment"),
                               value = keep(paste0("Ec_", i), default_Ec), min = 0, step = 1)),
        column(8, sliderInput(paste0("cc_", i), "Voluntary contribution rate",
                              min = 0, max = 1, step = 0.05,
                              value = keep(paste0("cc_", i), rep_len(default_c, i)[i])))
      )
    })
  })
  
  output$crisis_active_stock_inputs <- renderUI({
    n <- req(input$n)
    lapply(seq_len(n), function(i) {
      sliderInput(paste0("sc_", i), paste0("Player ", i, ": crisis stockpile rate"),
                  min = 0, max = 1, step = 0.05,
                  value = keep(paste0("sc_", i), rep_len(default_s, i)[i]))
    })
  })
  
  output$post_pg_inputs <- renderUI({
    n <- req(input$n)
    lapply(seq_len(n), function(i) {
      fluidRow(
        column(4, numericInput(paste0("Ep_", i), paste0("Player ", i, ": endowment"),
                               value = keep(paste0("Ep_", i), default_E), min = 0, step = 1)),
        column(8, sliderInput(paste0("cp_", i), "Voluntary contribution rate",
                              min = 0, max = 1, step = 0.05,
                              value = keep(paste0("cp_", i), rep_len(default_c, i)[i])))
      )
    })
  })
  
  output$post_stock_inputs <- renderUI({
    n <- req(input$n)
    lapply(seq_len(n), function(i) {
      sliderInput(paste0("sp_", i), paste0("Player ", i, ": stockpile rate"),
                  min = 0, max = 1, step = 0.05,
                  value = keep(paste0("sp_", i), rep_len(default_s, i)[i]))
    })
  })
  
  get_vec <- function(prefix, n) {
    v <- vapply(seq_len(n), function(i) {
      x <- input[[paste0(prefix, i)]]
      if (is.null(x) || is.na(x)) NA_real_ else x
    }, numeric(1))
    req(!anyNA(v))
    v
  }
  
  # Penalty settings shared by all phases
  penalty_args <- function() {
    req(input$penalty_type, input$endow_mode)
    if (input$penalty_type %in% c("flat", "per_unit")) req(input$penalty)
    list(penalty = if (is.null(input$penalty) || is.na(input$penalty)) 0 else input$penalty,
         type = input$penalty_type)
  }
  
  # ---- Normal rounds before the crisis (Phase 1 and Phase 2)
  sim <- reactive({
    n <- req(input$n)
    req(input$tax, input$S, input$mult, input$rounds)
    pa <- penalty_args()
    E  <- get_vec("E_", n)
    cr <- get_vec("c_", n)
    sr <- get_vec("s_", n)
    set.seed(input$seed)
    simulate_normal(
      E = E, tax = input$tax, S = input$S, penalty = pa$penalty, penalty_type = pa$type,
      mult = input$mult, rounds = input$rounds, c_rates = cr, s_rates = sr,
      noise_sd = input$noise, endow_mode = input$endow_mode
    )
  })
  
  # ---- Crisis rounds, starting from each player's stock and status after the normal rounds
  crisis <- reactive({
    n <- req(input$n)
    req(input$crisis_rounds, input$S_crisis, input$crisis_pg_mode)
    pa   <- penalty_args()
    d    <- sim()
    last <- d[d$round == max(d$round), ]
    set.seed(input$seed + 1)
    
    if (input$crisis_pg_mode == "offline") {
      req(input$mult_stock)
      kr  <- get_vec("k_", n)
      raw <- simulate_crisis(
        stock0 = last$stock, S = input$S_crisis, penalty = pa$penalty, penalty_type = pa$type,
        mult = input$mult_stock, rounds = input$crisis_rounds, k_rates = kr,
        noise_sd = input$noise, removed0 = last$removed_end, nobonus0 = last$bonus_forfeited
      )
      unify_crisis("offline", raw, mult_offline = input$mult_stock)
    } else {
      req(input$crisis_tax, input$crisis_mult)
      Ec  <- get_vec("Ec_", n)
      ccr <- get_vec("cc_", n)
      scr <- get_vec("sc_", n)
      raw <- simulate_normal(
        E = Ec, tax = input$crisis_tax, S = input$S_crisis, penalty = pa$penalty, penalty_type = pa$type,
        mult = rep(input$crisis_mult, input$crisis_rounds), rounds = input$crisis_rounds,
        c_rates = ccr, s_rates = scr, noise_sd = input$noise, stock0 = last$stock, round_offset = 0,
        thr = NULL, endow_mode = "each_round", removed0 = last$removed_end, nobonus0 = last$bonus_forfeited
      )
      unify_crisis("active", raw, mult_offline = NA)
    }
  })
  
  # ---- Post-crisis normal rounds (NULL when set to 0 rounds)
  post <- reactive({
    n <- req(input$n)
    req(!is.null(input$rounds_post), !is.na(input$rounds_post))
    req(input$tax_post, input$S_post, input$rebuild_mode)
    rp <- input$rounds_post
    if (rp < 1) return(NULL)
    pa   <- penalty_args()
    mode <- input$rebuild_mode
    
    thr <- NULL
    if (mode == "constant") {
      req(input$mult_post)
      mults <- rep(input$mult_post, rp)
    } else if (mode == "steps") {
      req(input$mult_start, input$mult_step, input$mult_every, input$mult_max)
      mults <- mult_schedule(rp, input$mult_start, input$mult_step, input$mult_every, input$mult_max)
    } else {
      req(input$thr_low, input$thr_amount, input$thr_high)
      mults <- rep(NA_real_, rp)
      thr   <- list(low = input$thr_low, high = input$thr_high, amount = input$thr_amount)
    }
    
    cd   <- crisis()
    last <- cd[cd$round == max(cd$round), ]
    E  <- get_vec("Ep_", n)
    cr <- get_vec("cp_", n)
    sr <- get_vec("sp_", n)
    set.seed(input$seed + 2)
    simulate_normal(
      E = E, tax = input$tax_post, S = input$S_post, penalty = pa$penalty, penalty_type = pa$type,
      mult = mults, rounds = rp, c_rates = cr, s_rates = sr, noise_sd = input$noise,
      stock0 = last$stock_end, round_offset = input$rounds + input$crisis_rounds, thr = thr,
      endow_mode = input$endow_mode, removed0 = last$removed_end, nobonus0 = last$bonus_forfeited
    )
  })
  
  post_needed <- function() {
    pd <- post()
    validate(need(!is.null(pd), "Set at least one normal round after the crisis to see this."))
    pd
  }
  
  # ---- Whole game in one long table (also used for the CSV download)
  all_rounds <- reactive({
    nd <- sim(); cd <- crisis(); pd <- post()
    from_normal <- function(d, phase) data.frame(
      phase = phase, round = d$round, player = d$player, active = d$active,
      multiplier = d$multiplier, endowment = d$endowment, tax_paid = d$tax_paid,
      survival_paid = d$survival_paid, survival_unpaid = d$unpaid,
      discretionary = d$discretionary, available = d$discretionary, stock_start = NA_real_,
      contribution = d$contribution, kept = d$kept, wallet_end = d$wallet_end,
      pool_share = d$pool_share, spendable = d$spendable, to_stock = d$to_stock,
      penalty = d$penalty, earnings = d$bonus, stock_end = d$stock,
      bonus_forfeited = d$bonus_forfeited, removed = d$removed_end
    )
    parts <- list(from_normal(nd, "normal_before_crisis"))
    parts[[2]] <- data.frame(
      phase = "crisis", round = input$rounds + cd$round, player = cd$player, active = cd$active,
      multiplier = cd$multiplier, endowment = cd$endowment, tax_paid = cd$tax_paid,
      survival_paid = cd$survival_paid, survival_unpaid = cd$unpaid,
      discretionary = cd$discretionary, available = cd$available, stock_start = cd$stock_start,
      contribution = cd$contribution, kept = cd$kept, wallet_end = NA_real_,
      pool_share = cd$pool_share, spendable = cd$spendable, to_stock = cd$to_stock,
      penalty = cd$penalty, earnings = cd$bonus, stock_end = cd$stock_end,
      bonus_forfeited = cd$bonus_forfeited, removed = cd$removed_end
    )
    if (!is.null(pd)) parts[[3]] <- from_normal(pd, "normal_after_crisis")
    d <- do.call(rbind, parts)
    d$cum_earnings <- ave(d$earnings, d$player, FUN = cumsum)
    d
  })
  
  # ---- Download
  output$download_rounds <- downloadHandler(
    filename = function() paste0("pgg_per_round_data_", format(Sys.Date(), "%Y%m%d"), ".csv"),
    content = function(file) {
      d <- all_rounds()
      d$player <- as.character(d$player)
      write.csv(d, file, row.names = FALSE, na = "")
    }
  )
  
  surv_height <- function() {
    n <- input$n
    if (is.null(n) || is.na(n)) n <- 4
    max(170, 100 + 30 * n)
  }
  
  # ---- Phase 1 outputs
  output$setup <- renderTable({
    d <- subset(sim(), round == 1,
                select = c(player, endowment, tax_paid, survival_paid, unpaid, discretionary))
    names(d) <- c("Player", "Endowment", "Tax paid", "Survival paid", "Survival unpaid", "Discretionary")
    d
  }, digits = 2)
  
  output$plot_contrib <- renderPlot({
    line_plot(sim(), "contribution", "Voluntary contribution per round", "Contribution")
  })
  
  output$plot_spendable <- renderPlot({
    line_plot(sim(), "spendable", "Spendable income per round", "Spendable income")
  })
  
  output$plot_survival1 <- renderPlot({
    survival_plot(sim(), "Survival cost met? (before the crisis)")
  }, height = surv_height)
  
  output$totals1 <- renderTable({
    tot <- aggregate(cbind(tax_paid, contribution, kept, pool_share, spendable) ~ player, sim(), sum)
    names(tot) <- c("Player", "Tax paid", "Contributed", "Kept", "Pool share received", "Spendable income")
    tot
  }, digits = 2)
  
  output$detail1 <- renderTable({
    d <- subset(sim(), select = c(round, player, endowment, tax_paid, survival_paid,
                                  contribution, kept, pool_share, spendable))
    names(d) <- c("Round", "Player", "Endowment", "Tax", "Survival", "Contribution",
                  "Kept", "Pool share", "Spendable")
    d
  }, digits = 2)
  
  # ---- Phase 2 outputs
  output$plot_stock <- renderPlot({
    line_plot(sim(), "stock", "Stockpile size", "Stock")
  })
  
  output$plot_bonus <- renderPlot({
    line_plot(sim(), "cum_bonus", "Cumulative bonus", "Bonus")
  })
  
  output$totals2 <- renderTable({
    d <- sim()
    tot <- aggregate(cbind(spendable, to_stock, penalty, bonus) ~ player, d, sum)
    fin <- d[d$round == max(d$round), c("player", "stock")]
    tot <- merge(tot, fin, by = "player")
    tot <- tot[, c("player", "spendable", "to_stock", "stock", "penalty", "bonus")]
    names(tot) <- c("Player", "Spendable income", "Sent to stockpile", "Final stock",
                    "Penalties", "Total bonus (net)")
    tot
  }, digits = 2)
  
  output$detail2 <- renderTable({
    d <- subset(sim(), select = c(round, player, spendable, to_stock, penalty, bonus, stock, cum_bonus))
    names(d) <- c("Round", "Player", "Spendable", "To stockpile", "Penalty", "Bonus (net)",
                  "Stock", "Cumulative bonus")
    d
  }, digits = 2)
  
  # ---- Crisis outputs
  output$crisis_setup <- renderTable({
    d <- crisis()
    d <- d[d$round == 1, c("player", "stock_start")]
    d$cover <- if (input$S_crisis > 0) d$stock_start / input$S_crisis else NA_real_
    names(d) <- c("Player", "Stock at crisis start", "Crisis rounds of survival covered")
    d
  }, digits = 2)
  
  output$plot_stock_crisis <- renderPlot({
    R  <- input$rounds
    n1 <- subset(sim(), select = c(round, player, stock))
    c1 <- crisis()
    c1 <- data.frame(round = R + c1$round, player = c1$player, stock = c1$stock_end)
    d  <- rbind(n1, c1)
    line_plot(d, "stock", "Stockpile through the crisis", "Stock") +
      crisis_layers(R, input$crisis_rounds, FALSE, max(d$stock), "crisis begins")
  })
  
  output$plot_crisis_contrib <- renderPlot({
    ttl <- if (identical(input$crisis_pg_mode, "active")) {
      "Voluntary contribution to the crisis public good"
    } else "Contribution to the stockpile pool"
    line_plot(crisis(), "contribution", ttl, "Contribution", xlab = "Crisis round")
  })
  
  output$plot_survival_crisis <- renderPlot({
    survival_plot(crisis(), "Survival cost met? (crisis rounds)", xlab = "Crisis round")
  }, height = surv_height)
  
  output$crisis_totals <- renderTable({
    d   <- crisis()
    tot <- aggregate(cbind(survival_paid, unpaid, penalty, contribution, pool_share) ~ player, d, sum)
    st  <- d[d$round == 1, c("player", "stock_start")]
    fin <- d[d$round == max(d$round), c("player", "stock_end")]
    tot <- merge(merge(st, tot, by = "player"), fin, by = "player")
    if (identical(input$crisis_pg_mode, "active")) {
      extra <- aggregate(cbind(tax_paid, bonus) ~ player, d, sum)
      tot   <- merge(tot, extra, by = "player")
      tot <- tot[, c("player", "stock_start", "tax_paid", "survival_paid", "unpaid", "penalty",
                     "contribution", "pool_share", "bonus", "stock_end")]
      names(tot) <- c("Player", "Start stock", "Tax paid", "Survival paid", "Survival unpaid", "Penalties",
                      "Contributed to PG", "Pool share received", "Bonus (net)", "Final stock")
    } else {
      tot <- tot[, c("player", "stock_start", "survival_paid", "unpaid", "penalty",
                     "contribution", "pool_share", "stock_end")]
      names(tot) <- c("Player", "Start stock", "Survival paid", "Survival unpaid", "Penalties",
                      "Contributed to pool", "Pool share received", "Final stock")
    }
    tot
  }, digits = 2)
  
  output$crisis_detail <- renderTable({
    d <- crisis()
    if (identical(input$crisis_pg_mode, "active")) {
      d <- subset(d, select = c(round, player, endowment, tax_paid, survival_paid, unpaid,
                                contribution, kept, pool_share, spendable, to_stock, bonus, stock_end))
      names(d) <- c("Crisis round", "Player", "Endowment", "Tax", "Survival paid", "Survival unpaid",
                    "Contribution", "Kept", "Pool share", "Spendable", "To stockpile", "Bonus (net)",
                    "Stock at end")
    } else {
      d <- subset(d, select = c(round, player, stock_start, survival_paid, unpaid,
                                contribution, pool_share, penalty, stock_end))
      names(d) <- c("Crisis round", "Player", "Stock at start", "Survival paid", "Survival unpaid",
                    "Contribution", "Pool share", "Penalty", "Stock at end")
    }
    d
  }, digits = 2)
  
  # ---- Phase 4a outputs (post-crisis public good)
  output$post_status <- renderText({
    pd <- post()
    if (is.null(pd) || !identical(input$rebuild_mode, "threshold") || is.na(input$thr_amount)) return("")
    g   <- unique(pd[, c("round", "cum_group_contrib")])
    hit <- which(g$cum_group_contrib >= input$thr_amount)
    if (length(hit) == 0) {
      paste0("Threshold not reached: the group contributed ", round(max(g$cum_group_contrib), 2),
             " of ", input$thr_amount, ".")
    } else {
      r <- g$round[hit[1]]
      if (r == max(g$round)) {
        paste0("Threshold reached in the final round (round ", r, "), so no rounds run at the maximum multiplier.")
      } else {
        paste0("Threshold reached after round ", r, ": maximum multiplier from round ", r + 1, ".")
      }
    }
  })
  
  output$post_setup <- renderTable({
    pd <- post_needed()
    d <- pd[pd$round == min(pd$round),
            c("player", "endowment", "tax_paid", "survival_paid", "unpaid", "discretionary")]
    names(d) <- c("Player", "Endowment", "Tax paid", "Survival paid", "Survival unpaid", "Discretionary")
    d
  }, digits = 2)
  
  output$plot_mult <- renderPlot({
    pd <- post_needed()
    d  <- unique(pd[, c("round", "multiplier")])
    ggplot(d, aes(round, multiplier)) +
      geom_step(linewidth = 1, colour = "grey30", direction = "hv") +
      geom_point(colour = "grey30") +
      scale_x_continuous(breaks = d$round) +
      expand_limits(y = 0) +
      labs(title = "Public good multiplier per round", x = "Round (whole game)", y = "Multiplier") +
      theme_minimal(base_size = 13)
  })
  
  output$plot_post_cumgroup <- renderPlot({
    pd <- post_needed()
    g  <- unique(pd[, c("round", "cum_group_contrib")])
    p  <- ggplot(g, aes(round, cum_group_contrib)) +
      geom_line(linewidth = 1, colour = "grey30") + geom_point(colour = "grey30")
    if (identical(input$rebuild_mode, "threshold") && !is.na(input$thr_amount)) {
      p <- p +
        geom_hline(yintercept = input$thr_amount, linetype = "dashed", colour = "firebrick") +
        annotate("text", x = min(g$round), y = input$thr_amount, label = "threshold",
                 hjust = 0, vjust = -0.5, colour = "firebrick", size = 4)
    }
    p + scale_x_continuous(breaks = g$round) +
      expand_limits(y = 0) +
      labs(title = "Cumulative group voluntary contributions", x = "Round (whole game)",
           y = "Points contributed") +
      theme_minimal(base_size = 13)
  })
  
  output$plot_post_contrib <- renderPlot({
    line_plot(post_needed(), "contribution", "Voluntary contribution per round", "Contribution",
              xlab = "Round (whole game)")
  })
  
  output$plot_post_spendable <- renderPlot({
    line_plot(post_needed(), "spendable", "Spendable income per round", "Spendable income",
              xlab = "Round (whole game)")
  })
  
  output$plot_survival_post <- renderPlot({
    survival_plot(post_needed(), "Survival cost met? (after the crisis)", xlab = "Round (whole game)")
  }, height = surv_height)
  
  output$post_totals1 <- renderTable({
    pd  <- post_needed()
    tot <- aggregate(cbind(tax_paid, contribution, kept, pool_share, spendable) ~ player, pd, sum)
    names(tot) <- c("Player", "Tax paid", "Contributed", "Kept", "Pool share received", "Spendable income")
    tot
  }, digits = 2)
  
  output$post_detail1 <- renderTable({
    d <- subset(post_needed(), select = c(round, player, multiplier, endowment, tax_paid, survival_paid,
                                          contribution, kept, pool_share, spendable))
    names(d) <- c("Round", "Player", "Multiplier", "Endowment", "Tax", "Survival", "Contribution",
                  "Kept", "Pool share", "Spendable")
    d
  }, digits = 2)
  
  # ---- Phase 4b outputs (post-crisis stockpile)
  output$plot_post_stock <- renderPlot({
    line_plot(post_needed(), "stock", "Stockpile size", "Stock", xlab = "Round (whole game)")
  })
  
  output$plot_post_bonus <- renderPlot({
    line_plot(post_needed(), "cum_bonus", "Cumulative bonus (post-crisis)", "Bonus",
              xlab = "Round (whole game)")
  })
  
  output$post_totals2 <- renderTable({
    pd  <- post_needed()
    tot <- aggregate(cbind(spendable, to_stock, penalty, bonus) ~ player, pd, sum)
    fin <- pd[pd$round == max(pd$round), c("player", "stock")]
    tot <- merge(tot, fin, by = "player")
    tot <- tot[, c("player", "spendable", "to_stock", "stock", "penalty", "bonus")]
    names(tot) <- c("Player", "Spendable income", "Sent to stockpile", "Final stock",
                    "Penalties", "Total bonus (net)")
    tot
  }, digits = 2)
  
  output$post_detail2 <- renderTable({
    d <- subset(post_needed(), select = c(round, player, spendable, to_stock, penalty, bonus, stock, cum_bonus))
    names(d) <- c("Round", "Player", "Spendable", "To stockpile", "Penalty", "Bonus (net)",
                  "Stock", "Cumulative bonus")
    d
  }, digits = 2)
  
  # ---- Overall outcomes
  output$plot_stock_all <- renderPlot({
    d <- all_rounds()
    R <- input$rounds; K <- input$crisis_rounds
    line_plot(d, "stock_end", "1. Stockpile over the whole game", "Stock") +
      crisis_layers(R, K, max(d$round) > R + K, max(d$stock_end, na.rm = TRUE))
  })
  
  output$plot_earnings_all <- renderPlot({
    d <- all_rounds()
    R <- input$rounds; K <- input$crisis_rounds
    line_plot(d, "cum_earnings", "2. Bonus earned over the whole game (net of penalties)", "Cumulative bonus") +
      crisis_layers(R, K, max(d$round) > R + K, max(d$cum_earnings, na.rm = TRUE))
  })
  
  output$plot_survival_all <- renderPlot({
    survival_plot(all_rounds(), "Survival cost met? (whole game)")
  }, height = surv_height)
  
  # Group indicators per round
  output$plot_indicators <- renderPlot({
    d <- all_rounds()
    R <- input$rounds; K <- input$crisis_rounds
    rounds <- sort(unique(d$round))
    rows <- lapply(rounds, function(r) {
      x <- d[d$round == r & d$active, ]
      avail <- sum(x$available, na.rm = TRUE)
      data.frame(
        round = r,
        `Survival cost met` = if (nrow(x) > 0) mean(x$survival_unpaid == 0) else NA_real_,
        `Contributed share of available money` = if (avail > 0) sum(x$contribution, na.rm = TRUE) / avail else NA_real_,
        check.names = FALSE
      )
    })
    w <- do.call(rbind, rows)
    long <- data.frame(
      round = rep(w$round, 2),
      value = c(w[[2]], w[[3]]),
      indicator = rep(names(w)[2:3], each = nrow(w))
    )
    ggplot(long, aes(round, value, colour = indicator)) +
      crisis_layers(R, K, max(d$round) > R + K, 1) +
      geom_line(linewidth = 1, na.rm = TRUE) + geom_point(na.rm = TRUE) +
      scale_x_continuous(breaks = rounds) +
      scale_y_continuous(labels = function(x) paste0(100 * x, "%"), limits = c(0, 1)) +
      labs(title = "3. Group survival and cooperation", x = "Round", y = NULL, colour = NULL) +
      theme_minimal(base_size = 13) +
      theme(legend.position = "bottom")
  })
  
  output$indicators <- renderTable({
    d      <- all_rounds()
    R      <- input$rounds; K <- input$crisis_rounds
    n      <- nlevels(d$player)
    need   <- input$S_crisis * K
    blocks <- list(
      `Before crisis` = d[d$phase == "normal_before_crisis", ],
      `Crisis`        = d[d$phase == "crisis", ],
      `After crisis`  = d[d$phase == "normal_after_crisis", ],
      `Whole game`    = d
    )
    pct <- function(x) ifelse(is.na(x), "-", sprintf("%.0f%%", 100 * x))
    num <- function(x) sprintf("%.2f", x)
    
    surv <- sapply(blocks, function(x) {
      x <- x[x$active, ]
      if (nrow(x) == 0) NA_real_ else mean(x$survival_unpaid == 0)
    })
    coop <- sapply(blocks, function(x) {
      x <- x[x$active, ]
      a <- sum(x$available, na.rm = TRUE)
      if (a > 0) sum(x$contribution, na.rm = TRUE) / a else NA_real_
    })
    pen   <- sapply(blocks, function(x) sum(x$penalty, na.rm = TRUE))
    bonus <- sapply(blocks, function(x) sum(x$earnings, na.rm = TRUE))
    
    st_start <- d[d$round == R, ]
    enough   <- mean(st_start$stock_end >= need - 1e-9)
    last     <- d[d$round == max(d$round), ]
    forf     <- sum(last$bonus_forfeited)
    remv     <- sum(last$removed)
    
    blank <- c("-", "-", "-")
    data.frame(
      Indicator = c(
        paste0("Players with enough stock to cover the crisis (stock of at least ", num(need), ")"),
        "Player-rounds with the survival cost met",
        "Cooperation: share of available money contributed",
        "Penalty points (total, all players)",
        "Bonus earned, net of penalties (total, all players)",
        "Players who lost their bonus (by the end)",
        "Players removed from the game (by the end)"
      ),
      `Before crisis` = c(pct(enough), pct(surv[1]), pct(coop[1]), num(pen[1]), num(bonus[1]), "-", "-"),
      `Crisis`        = c("-", pct(surv[2]), pct(coop[2]), num(pen[2]), num(bonus[2]), "-", "-"),
      `After crisis`  = c("-", pct(surv[3]), pct(coop[3]), num(pen[3]), num(bonus[3]), "-", "-"),
      `Whole game`    = c("-", pct(surv[4]), pct(coop[4]), num(pen[4]), num(bonus[4]),
                          paste0(forf, " of ", n), paste0(remv, " of ", n)),
      check.names = FALSE
    )
  })
  
  output$payoff <- renderTable({
    d       <- all_rounds()
    req(!is.null(input$cashout), !is.na(input$cashout))
    players <- levels(d$player)
    R <- input$rounds; K <- input$crisis_rounds
    before  <- d[d$phase == "normal_before_crisis", ]
    during  <- d[d$phase == "crisis", ]
    after   <- d[d$phase == "normal_after_crisis", ]
    at_round <- function(rr, col) {
      x <- d[d$round == rr, ]
      setNames(x[[col]], as.character(x$player))[players]
    }
    bonus_before <- sum_by_player(before, "earnings", players)
    crisis_pen   <- sum_by_player(during, "penalty", players)
    bonus_after  <- sum_by_player(after, "earnings", players)
    final_stock  <- at_round(max(d$round), "stock_end")
    forfeited    <- at_round(max(d$round), "bonus_forfeited") | at_round(max(d$round), "removed")
    cash         <- ifelse(forfeited, 0, input$cashout * final_stock)
    status       <- ifelse(at_round(max(d$round), "removed"), "Removed",
                           ifelse(at_round(max(d$round), "bonus_forfeited"), "No bonus", "Active"))
    short_rounds <- sum_by_player(transform(d, short = as.numeric(survival_unpaid > 0)), "short", players)
    out <- data.frame(
      Player = players,
      before = bonus_before, pen = crisis_pen, after = bonus_after,
      s_start = at_round(R, "stock_end"), s_end = at_round(R + K, "stock_end"),
      s_final = final_stock, cash = cash,
      total = bonus_before - crisis_pen + bonus_after + cash,
      short = as.integer(short_rounds), status = status
    )
    names(out) <- c("Player", "Bonus before crisis (net)", "Crisis penalties", "Bonus after crisis (net)",
                    "Stock at crisis start", "Stock at crisis end", "Final stock", "Stock cash-out",
                    "Total payoff", "Rounds with unmet survival", "Status at end")
    out
  }, digits = 2)
  
  # ---- Game log
  output$game_log <- renderUI({
    d <- all_rounds()
    R <- input$rounds; K <- input$crisis_rounds
    rounds <- sort(unique(d$round))
    tagList(lapply(rounds, function(r) build_round_block(d, r, R, K)))
  })
}

shinyApp(ui, server)