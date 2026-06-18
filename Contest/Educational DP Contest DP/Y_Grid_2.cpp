#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e9 + 7;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int expo(int a, int b){
    int res = 1;
    while(b > 0){
        if(b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}

int mminvprime(int a){
    return expo(a, mod - 2);
}

const int N = 3005, MAXN = 2e5 + 10;
int n, h, w, dp[N][2], all_path, fact[MAXN], ifact[MAXN];
pair<int,int> wall[N];

int calc(int a, int b){
    return ((fact[a + b] * ifact[a]) % mod * ifact[b]) % mod;
}

void input(){
    cin >> h >> w >> n;
    for(int i = 0; i < n; i++){
        for(int k = 0; k < 2; k++){
            dp[i][k] = -1;
        }
    }
    for(int i = 0; i < n; i++){
        cin >> wall[i].first >> wall[i].second;
    }
    sort(wall, wall + n);
}

int f(int i, int j){
    int &ans = dp[i][j];
    if(ans != -1)
        return ans;
    if(j & 1)
        ans = calc(h - wall[i].first, w - wall[i].second);
    else
        ans = mod - calc(h - wall[i].first, w - wall[i].second);
    for(int k = i + 1; k < n; k++){
        if(wall[k].first >= wall[i].first and wall[k].second >= wall[i].second){
            ans = (ans + (calc(wall[k].first - wall[i].first, wall[k].second - wall[i].second) * f(k, j ^ 1)) % mod + mod) % mod;
        }
    }
    return ans;
}

void solve()
{
    input();
    all_path = calc(h - 1 , w - 1);
    for(int i = 0; i < n; i++){
        all_path = (all_path - (calc(wall[i].first - 1, wall[i].second - 1) * f(i, 1)) % mod + mod) % mod;
    }
    cout << all_path << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);

    fact[0] = 1;
    for(int i = 1; i < MAXN; i++){
        fact[i] = (fact[i - 1] * i) % mod;
    }
    ifact[MAXN - 1] = mminvprime(fact[MAXN - 1]);
    for(int i = MAXN - 2; i >= 0; i--){
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
    }

    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}