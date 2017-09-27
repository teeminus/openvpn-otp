#include <config.h>

#include <stdio.h>
#include <stdint.h>
#include <endian.h>
#include <string.h>
#include <ctype.h>
#include <inttypes.h>

#ifndef htobe64
#include <netinet/in.h>
#endif

#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/sha.h>

#ifdef HAVE_OPENVPN_OPENVPN_PLUGIN_H
#include "openvpn/openvpn-plugin.h"
#elif HAVE_OPENVPN_PLUGIN_H
#include "openvpn-plugin.h"
#endif

#include "base32.h"
#include "hex.h"
#define MAXWORDLEN 256


static char *otp_secrets = "/etc/ppp/otp-secrets";
static char *hotp_counters = "/var/spool/openvpn/hotp-counters/";
static int otp_slop = 180;

static int totp_t0 = 0;
static int totp_step = 30;
static int totp_digits = 6;

static int motp_step = 10;

static int hotp_syncwindow = 2;

static int debug = 0;

typedef struct user_entry {
    char name[MAXWORDLEN];
    char server[MAXWORDLEN];
    char secret[MAXWORDLEN];
    char addr[MAXWORDLEN];
} user_entry_t;

typedef struct otp_params {
    const char *method;
    const char *hash;
    const char *encoding;
    const char *key;
    const char *pin;
    const char *udid;
} otp_params_t;

struct plugin {
    plugin_log_t log;
};

#define LOG(format, ...) plugin->log(PLOG_NOTE,  "OTP-AUTH", format, ## __VA_ARGS__)

#define DEBUG(format, ...) if (debug > 0) plugin->log(PLOG_NOTE, "OTP-AUTH-DEBUG", format, ## __VA_ARGS__)

#ifndef htobe64

static uint64_t
htobe64(uint64_t value)
{
#if __BYTE_ORDER == __LITTLE_ENDIAN
    uint32_t low = htonl(value);
    uint32_t high = htonl(value >> 32);
    return (((uint64_t)low) << 32) | high;
#elif __BYTE_ORDER == __BIG_ENDIAN
    return value;
#else
#error "Unknown BYTE_ORDER"
#endif
}

#endif




static void
seek_eoln(FILE *secrets_file)
{
    while (!feof(secrets_file) && '\n' != fgetc(secrets_file)) {
        // Do nothing
    }
}


static int
read_word(FILE *secrets_file, char word[MAXWORDLEN])
{
    char ch = 0;
    char *p = word;
    char *q = word + MAXWORDLEN - 1;
    char quote = 0;

    while (!feof(secrets_file) && isspace((ch = fgetc(secrets_file)))) {
        // Do nothing
    }

    while (!feof(secrets_file)) {
        if (quote) {
            if (ch == quote) {
                quote = 0;
            }
            else {
                *p++ = ch;
            }
        }
        else if (isspace(ch) || '#' == ch) {
            *p = *q = 0;
            return ch;
        }
        else if ('\'' == ch || '"' == ch) {
            quote = ch;
        }
        else if ('\\' == ch) {
            *p = fgetc(secrets_file);
            if ('\n' != *p) {
                ++p;
            }
        }
        else {
            *p++ = ch;
        }

        if (p > q) {
            return -1;
        }

        ch = fgetc(secrets_file);
    }

    return -1;
}


static int
read_user_entry(FILE *secrets_file, user_entry_t *user_entry)
{
    int rc;

retry:
    if (feof(secrets_file)) {
        return -1;
    }

    rc = read_word(secrets_file, user_entry->name);
    if ('#' == rc || -1 == rc) {
        seek_eoln(secrets_file);
        goto retry;
    }

    if ('\n' == rc) {
        goto retry;
    }

    rc = read_word(secrets_file, user_entry->server);
    if ('#' == rc || -1 == rc) {
        seek_eoln(secrets_file);
        goto retry;
    }

    if ('\n' == rc) {
        goto retry;
    }

    rc = read_word(secrets_file, user_entry->secret);
    if ('#' == rc || -1 == rc) {
        seek_eoln(secrets_file);
        goto retry;
    }

    if ('\n' == rc) {
        goto retry;
    }

    rc = read_word(secrets_file, user_entry->addr);
    if (-1 == rc) {
        seek_eoln(secrets_file);
        goto retry;
    }

    if ('\n' != rc) {
        seek_eoln(secrets_file);
    }

    return 0;
}


static int
split_secret(char *secret, otp_params_t *otp_params)
{
    char *p = secret;

    otp_params->method = p;
    if (NULL == (p = strchr(p, ':'))) {
        return -1;
    }
    *p++ = 0;

    otp_params->hash = p;
    if (NULL == (p = strchr(p, ':'))) {
        return -1;
    }
    *p++ = 0;

    otp_params->encoding = p;
    if (NULL == (p = strchr(p, ':'))) {
        return -1;
    }
    *p++ = 0;

    otp_params->key = p;
    if (NULL == (p = strchr(p, ':'))) {
        return -1;
    }
    *p++ = 0;

    otp_params->pin = p;
    if (NULL != (p = strchr(p, ':'))) {
        *p++ = 0;
    }

    otp_params->udid = p;

    if (p && strchr(p, ':')) {
        return -1;
    }

    return 0;
}

static int
hotp_read_counter(const void * otp_key, struct plugin *plugin)
{
    /* Compute SHA1 for the otp_key */
    unsigned char hash[SHA_DIGEST_LENGTH];
    unsigned char hexdigest[SHA_DIGEST_LENGTH*2];
    char line[256];
    char path[256];
    FILE *counter_file;
    int i;

    SHA1(otp_key, strlen(otp_key), hash);

    for (i = 0; i < 20; i++) {
        sprintf(&hexdigest[i*2], "%02x", hash[i]);
    }
    snprintf(path, sizeof(path), "%s%s", hotp_counters, hexdigest);
    /* Find matching SHA1*/
    DEBUG("opening HOTP counter file '%s'", path);
    counter_file = fopen(path, "r");
    if (counter_file != NULL) {
        if (fgets(line, sizeof(line), counter_file)) {
          fclose(counter_file);
          int ret = atoi(line);
          DEBUG("current HOTP value is %i", ret);
          return atoi(line);
        }
        fclose(counter_file);
    }
    LOG("failed to read HOTP counter file '%s'", path);
    return -1;
}

static int
hotp_set_counter(const void * otp_key, int counter, struct plugin *plugin)
{
    /* Compute SHA1 for the otp_key */
    unsigned char hash[SHA_DIGEST_LENGTH];
    unsigned char hexdigest[SHA_DIGEST_LENGTH*2];
    char line[256];
    char path[256];
    FILE *counter_file;
    int i;

    SHA1(otp_key, strlen(otp_key), hash);

    for (i = 0; i < 20; i++) {
        sprintf(&hexdigest[i*2], "%02x", hash[i]);
    }
    snprintf(path, sizeof(path), "%s%s", hotp_counters, hexdigest);

    /* Find matching SHA1*/
    DEBUG("opening HOTP counter file '%s' for writing", path);
    counter_file = fopen(path, "w");
    if (counter_file != NULL) {
        DEBUG("setting HOTP counter value to %i", counter);
        if (fprintf(counter_file, "%d", counter)) {
          fclose(counter_file);
          DEBUG("HOTP counter update successful", counter);
          return 0;
        }
        fclose(counter_file);
    }
    LOG("failed to write HOTP counter file '%s'", path);
    return -1;
}

/**
 * Verify user name and password
 */
static int otp_verify(const char *vpn_username, const char *vpn_secret, struct plugin *plugin)
{
    FILE *secrets_file;
    user_entry_t user_entry;
    otp_params_t otp_params;

    const EVP_MD *otp_digest;
    char secret[256];
    uint8_t decoded_secret[256];
    int i;
    int ok = 0;

    secrets_file = fopen(otp_secrets, "r");
    if (NULL == secrets_file) {
        LOG("failed to open %s", otp_secrets);
        return ok;
    }

    DEBUG("trying to authenticate username '%s'", vpn_username);

    while (!feof(secrets_file)) {
        if (read_user_entry(secrets_file, &user_entry)) {
            continue;
        }

        if (strcmp(vpn_username, user_entry.name)) {
            continue;
        }

        DEBUG("username '%s' exists in '%s'", vpn_username, otp_secrets);

        /* Handle non-otp passwords before trying to parse out otp fields */
        if (!strncasecmp(user_entry.secret, "plain:", sizeof("plain:") - 1)) {
            const char *password = user_entry.secret + sizeof("plain:") - 1;
            if (vpn_username && !strcmp (vpn_username, user_entry.name)
                && vpn_secret && password && !strcmp (vpn_secret, password)) {
                ok = 1;
            }
            goto done;
        }

        if (split_secret(user_entry.secret, &otp_params)) {
            goto done;
        }

        otp_digest = EVP_get_digestbyname(otp_params.hash);
        if (!otp_digest) {
            LOG("unknown digest '%s'", otp_params.hash);
            goto done;
        }

        unsigned int key_len;
        const void * otp_key;

        if (!strcasecmp(otp_params.encoding, "base32")) {
            key_len = base32_decode((uint8_t *) otp_params.key, decoded_secret, sizeof(decoded_secret));
            otp_key = decoded_secret;
        } else
        if (!strcasecmp(otp_params.encoding, "hex")) {
            key_len = hex_decode(otp_params.key, decoded_secret, sizeof(decoded_secret));
            otp_key = decoded_secret;
        } else
        if (!strcasecmp(otp_params.encoding, "text")) {
            otp_key = otp_params.key;
            key_len = strlen(otp_params.key);
        } else {
            LOG("unknown encoding '%s'", otp_params.encoding);
            goto done;
        }

        uint64_t T, Tn, Ti;
        uint8_t mac[EVP_MAX_MD_SIZE];
        unsigned maclen;


        if (!strncasecmp("totp", otp_params.method, 4)) {
            HMAC_CTX *hmac = HMAC_CTX_new ();
            const uint8_t *otp_bytes;
            uint32_t otp, divisor = 1;
            int tstep = totp_step;
            int tdigits = totp_digits;
            if (!strcasecmp("totp-60-6", otp_params.method)) {
                tstep = 60;
                tdigits = 6;
            }
            int range = otp_slop / tstep;


            T = (time(NULL) - totp_t0) / tstep;

            for (i = 0; i < tdigits; ++i) {
                divisor *= 10;
            }

            for (i = -range; !ok && i <= range; ++i) {
                Tn = htobe64(T + i);

                HMAC_CTX_reset(hmac);
                HMAC_Init_ex(hmac, otp_key, key_len, otp_digest, NULL);
                HMAC_Update(hmac, (uint8_t *)&Tn, sizeof(Tn));
                HMAC_Final(hmac, mac, &maclen);

                otp_bytes = mac + (mac[maclen - 1] & 0x0f);
                otp = ((otp_bytes[0] & 0x7f) << 24) | (otp_bytes[1] << 16) |
                    (otp_bytes[2] << 8) | otp_bytes[3];
                otp %= divisor;

                snprintf(secret, sizeof(secret), "%s%0*u", otp_params.pin, tdigits, otp);

                DEBUG("trying method='%s', client_username='%s', client_secret='%s', server_username='%s', server_secret='%s'", otp_params.method, vpn_username, vpn_secret, user_entry.name, secret);

                if (vpn_username && !strcmp (vpn_username, user_entry.name)
                    && vpn_secret && !strcmp (vpn_secret, secret)) {
                    ok = 1;
                    DEBUG("auth ok for method='%s', client_username='%s', client_secret='%s'", otp_params.method, vpn_username, vpn_secret);
                }
            }
            HMAC_CTX_free (hmac);
        }
        else if (!strncasecmp("hotp", otp_params.method, 4)) {
            HMAC_CTX *hmac = HMAC_CTX_new();
            const uint8_t *otp_bytes;
            uint32_t otp, divisor = 1;
            int tdigits = totp_digits;
            int i = 0;

            i = hotp_read_counter(otp_params.key, plugin);

            if (i >= 0) {
              T = i;

              for (i = 0; i < tdigits; ++i) {
                  divisor *= 10;
              }

              for (i = 0; !ok && i <= hotp_syncwindow; i++) {
                  Ti = T+i;
                  Tn = htobe64(Ti);

                  HMAC_CTX_reset(hmac);
                  HMAC_Init_ex(hmac, otp_key, key_len, otp_digest, NULL);
                  HMAC_Update(hmac, (uint8_t *)&Tn, sizeof(Tn));
                  HMAC_Final(hmac, mac, &maclen);

                  otp_bytes = mac + (mac[maclen - 1] & 0x0f);
                  otp = ((otp_bytes[0] & 0x7f) << 24) | (otp_bytes[1] << 16) |
                         (otp_bytes[2] << 8) | otp_bytes[3];
                  otp %= divisor;

                  snprintf(secret, sizeof(secret), "%s%0*u", otp_params.pin, tdigits, otp);

                  DEBUG("trying method='%s', client_username='%s', client_secret='%s', server_username='%s', server_secret='%s', hotp=%"PRIu64"", otp_params.method, vpn_username, vpn_secret, user_entry.name, secret, Ti);

                  if (vpn_username && !strcmp (vpn_username, user_entry.name)
                      && vpn_secret && !strcmp (vpn_secret, secret)) {
                      ok = 1;
                      DEBUG("auth ok for method='%s', client_username='%s', client_secret='%s', hotp=%"PRIu64"", otp_params.method, vpn_username, vpn_secret, Ti);
                      hotp_set_counter(otp_params.key, Ti+1, plugin);
                  }
              }
            }
            HMAC_CTX_free (hmac);
        }
        else if (!strcasecmp("motp", otp_params.method)) {
            char buf[64];
            int n;
            int range = otp_slop / motp_step;

            T = time(NULL) / motp_step;

            for (i = -range; !ok && i <= range; ++i) {
                EVP_MD_CTX *ctx = EVP_MD_CTX_new();
                EVP_MD_CTX_init(ctx);
                EVP_DigestInit_ex(ctx, otp_digest, NULL);
                n = sprintf(buf, "%" PRIu64, T + i);
                EVP_DigestUpdate(ctx, buf, n);
                EVP_DigestUpdate(ctx, otp_key, key_len);
                EVP_DigestUpdate(ctx, otp_params.pin, strlen(otp_params.pin));
                if (otp_params.udid) {
                    int udid_len = strlen(otp_params.udid);
                    EVP_DigestUpdate(ctx, otp_params.udid, udid_len);
                }
                EVP_DigestFinal_ex(ctx, mac, &maclen);
                EVP_MD_CTX_cleanup(ctx);

                snprintf(secret, sizeof(secret),
                         "%02x%02x%02x", mac[0], mac[1], mac[2]);

                DEBUG("trying method='%s', client_username='%s', client_secret='%s', server_username='%s', server_secret='%s'", otp_params.method, vpn_username, vpn_secret, user_entry.name, secret);

                if (vpn_username && !strcmp (vpn_username, user_entry.name)
                    && vpn_secret && !strcmp (vpn_secret, secret)) {
                    ok = 1;
                    DEBUG("auth ok for method='%s', client_username='%s', client_secret='%s'", otp_params.method, vpn_username, vpn_secret);
                }
                EVP_MD_CTX_free (ctx);
            }
        }
        else {
            LOG("unknown OTP method %s", otp_params.method);
        }

    done:
        memset(secret, 0, sizeof(secret));

    }

    if (NULL != secrets_file) {
        fclose(secrets_file);
    }

    return ok;
}


/*
 * Given an environmental variable name, search
 * the envp array for its value, returning it
 * if found or NULL otherwise.
 */
static const char * get_env (const char *name, const char *envp[])
{
  if (envp)
    {
      int i;
      const int namelen = strlen (name);
      for (i = 0; envp[i]; ++i)
        {
          if (!strncmp (envp[i], name, namelen))
            {
              const char *cp = envp[i] + namelen;
              if (*cp == '=')
                return cp + 1;
            }
        }
    }
  return NULL;
}



/**
 * Plugin open (init)
 */
OPENVPN_EXPORT int
openvpn_plugin_open_v3(const int version,
                       struct openvpn_plugin_args_open_in const *args,
                       struct openvpn_plugin_args_open_return *rv)
{
  OpenSSL_add_all_digests();

  /* Init plugin wrapper */
  struct plugin *plugin = calloc(1, sizeof(struct plugin));
  plugin->log  = args->callbacks->plugin_log;

  /*
   * We are only interested in intercepting the
   * --auth-user-pass-verify callback.
   */
  rv->type_mask = OPENVPN_PLUGIN_MASK (OPENVPN_PLUGIN_AUTH_USER_PASS_VERIFY);


  /*
   * Set up configuration variables
   *
   */
  const char * cfg_otp_secrets = get_env("otp_secrets", args->argv);
  if (cfg_otp_secrets != NULL) {
     otp_secrets = strdup(cfg_otp_secrets);
  }
  LOG("otp_secrets=%s", otp_secrets);

  const char * cfg_hotp_counter_file = get_env("hotp_counters", args->argv);
  if (cfg_hotp_counter_file != NULL) {
     hotp_counters = strdup(cfg_hotp_counter_file);
  }
  LOG("hotp_counters=%s", hotp_counters);

  const char * cfg_otp_slop = get_env("otp_slop", args->argv);
  if (cfg_otp_slop != NULL) {
     otp_slop = atoi(cfg_otp_slop);
  }
  LOG("otp_slop=%i", otp_slop);

  const char * cfg_totp_t0 = get_env("totp_t0", args->argv);
  if (cfg_totp_t0 != NULL) {
     totp_t0 = atoi(cfg_totp_t0);
  }
  LOG("totp_t0=%i", totp_t0);

  const char * cfg_totp_step= get_env("totp_step", args->argv);
  if (cfg_totp_step != NULL) {
     totp_step = atoi(cfg_totp_step);
  }
  LOG("totp_step=%i", totp_step);

  const char * cfg_totp_digits = get_env("totp_digits", args->argv);
  if (cfg_totp_digits != NULL) {
     totp_digits = atoi(cfg_totp_digits);
  }
  LOG("totp_digits=%i", totp_digits);

  const char * cfg_motp_step = get_env("motp_step", args->argv);
  if (cfg_motp_step != NULL) {
     motp_step = atoi(cfg_motp_step);
  }
  LOG("motp_step=%i", motp_step);

  const char * cfg_hotp_syncwindow = get_env("hotp_syncwindow", args->argv);
  if (cfg_hotp_syncwindow != NULL) {
     hotp_syncwindow = atoi(cfg_hotp_syncwindow);
  }
  LOG("hotp_syncwindow=%i", hotp_syncwindow);

  const char * cfg_debug = get_env("debug", args->argv);
  if (cfg_debug != NULL) {
       debug = atoi(cfg_debug);
  }
  LOG("debug=%i", debug);
  DEBUG("debug mode has been enabled");

  rv->handle = (void *)plugin;
  return OPENVPN_PLUGIN_FUNC_SUCCESS;
}


/**
 * Check credentials
 */
OPENVPN_EXPORT int
openvpn_plugin_func_v3(const int version,
                       struct openvpn_plugin_args_func_in const *args,
                       struct openvpn_plugin_args_func_return *rv)
{
  /* get username/password from envp string array */
  const char *username = get_env ("username", args->envp);
  const char *password = get_env ("password", args->envp);
  const char *ip = get_env ("untrusted_ip", args->envp);
  const char *port = get_env ("untrusted_port", args->envp);
  const char *common_name = get_env ("common_name", args->envp);

  /* get plugin wrapper */
  struct plugin *plugin = (struct plugin  *)args->handle;

  /* check if envp strings are set */
  if ((username == NULL) || (password == NULL) || (ip == NULL) || (port == NULL) || (common_name == NULL)) {
    LOG("Failed to get env strings");
    return OPENVPN_PLUGIN_FUNC_ERROR;
  }

  const int ulen = strlen(username);
  const int pwlen = strlen(password);
  const int cnlen = strlen(common_name);
  if ( ulen > MAXWORDLEN || ulen == 0 || pwlen > MAXWORDLEN || pwlen == 0 || cnlen > MAXWORDLEN || cnlen == 0) {
    LOG("String length check failed => username (%d), password(%d), common_name(%d)", ulen, pwlen, cnlen);
    return OPENVPN_PLUGIN_FUNC_ERROR;
  }

  /* check if entered username and certificate name match */
  if ((ulen != cnlen) || (strncmp (username, common_name, ulen) != 0)) {
    LOG("common_name (%s) and username (%s) are not identical", common_name, username);
    return OPENVPN_PLUGIN_FUNC_ERROR;
  }
  /* check entered username/password against what we require */
  int ok = otp_verify(username, password, plugin);

  if (ok == 1) {
    LOG("authentication succeeded for username '%s', remote %s:%s", username, ip, port);
    return OPENVPN_PLUGIN_FUNC_SUCCESS;
  }
  else {
    LOG("authentication failed for username '%s', remote %s:%s", username, ip, port);
    return OPENVPN_PLUGIN_FUNC_ERROR;
  }
}



/**
 * Plugin close
 */
OPENVPN_EXPORT void
openvpn_plugin_close_v1 (openvpn_plugin_handle_t handle)
{
  struct plugin *plugin = (struct plugin *)handle;
  free(plugin);
}
