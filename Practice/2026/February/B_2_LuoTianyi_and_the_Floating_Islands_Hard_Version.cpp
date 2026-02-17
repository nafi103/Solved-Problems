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

const int N = 2e5 + 10;
int fact[N], ifact[N];

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

int nCr(int _n, int r){
    if(r > _n)
        return 0;
    return ((fact[_n] * ifact[r]) % mod * ifact[_n - r]) % mod;
}

int n, k, ans;
vector<vector<int>> t;
vector<int> subtree_size;

void dfs(int node, int par){
    subtree_size[node] = 1;
    for(auto &child: t[node]){
        if(child != par){
            dfs(child, node);
            subtree_size[node] += subtree_size[child];
        }
    }
}

void solve()
{
    cin >> n >> k;
    t.resize(n);
    subtree_size.resize(n);
    for(int i = 1; i < n; i++){
        int u, v;
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
    if(k&1){
        cout << 1 << endl;
        return;
    }
    ans = 0;
    dfs(0, -1);
    for(int i = 0; i < n; i++){
        ans = (ans + (nCr(subtree_size[i], k/2) * (nCr(n - subtree_size[i], k / 2))) % mod) % mod;
    }
    ans = (ans + nCr(n, k)) % mod;
    cout << (ans * mminvprime(nCr(n, k))) % mod << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);

    fact[0] = 1;
    for(int i = 1; i < N; i++){
        fact[i] = (fact[i - 1] * i) % mod;
    }
    ifact[N - 1] = mminvprime(fact[N - 1]);
    for(int i = N - 2; i >= 0; i--){
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
    }

    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}