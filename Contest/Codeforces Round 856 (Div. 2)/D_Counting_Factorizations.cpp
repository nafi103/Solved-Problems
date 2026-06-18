#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 const int N = 1e6 + 10, M = 4024;
bool prime[N];
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
 int fact[M], ifact[M];
vector<pair<int,int>> v;
vector<vector<int>> dp;
vector<int> suff;
int n, m;
 int f(int i, int j){
    if(i == m)
        return j == 0;
    if(j == 0)
        return suff[i];
    int &ans = dp[i][j];
    if(ans != -1)
        return ans;
    ans = (f(i + 1, j) * ifact[v[i].second]) % mod;
    if(prime[v[i].first])
        ans = (ans + (f(i + 1, j - 1) * ifact[v[i].second - 1]) % mod) % mod;
    return ans;
}
 void solve()
{
    cin >> n;
    map<int,int> mp;
    int x;
    for(int i = 0; i < 2 * n; i++){
        cin >> x;
        mp[x]++;
    }
    m = sz(mp);
    v.reserve(m);
    for(auto &[f,s]: mp){
        v.push_back({f, s});
    }
    suff.resize(m);
    for(int i = m - 1; i >= 0; i--){
        suff[i] = ifact[v[i].second];
        if(i < m - 1)
            suff[i] = (suff[i] * suff[i + 1]) % mod;
    }
    dp.assign(m, vector<int> (n + 1, -1));
    cout << (fact[n] * f(0, n)) % mod << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    memset(prime, true, sizeof prime);
    prime[0] = prime[1] = false;
    for(int i = 2; i * i < N; i++){
        if(prime[i]){
            for(int j = i * i; j < N; j += i)
                prime[j] = false;
        }
    }
     fact[0] = 1;
    for(int i = 1; i < M; i++){
        fact[i] = (fact[i - 1] * i) % mod;
    }
     ifact[M - 1] = mminvprime(fact[M - 1]);
    for(int i = M - 2; i >= 0; i--){
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
    }
     int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}