#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
const int N = 2e5 + 10;
vector<int> spf(N);

vector<int> get_primes(int x)
{
    vector<int> primes;
    while (x > 1)
    {
        int p = spf[x];
        primes.push_back(p);
        while (x % p == 0)
            x /= p;
    }
    return primes;
}

bool check(map<int, int> &mp, vector<pair<int, int>> &a)
{
    for (auto &[x, c] : a)
    {
        vector<int> primes = get_primes(x);
        for (auto &p : primes)
        {
            mp[p]++;
            if (mp[p] > 1)
                return true;
        }
    }
    return false;
}

int one_check(map<int, int> &mp, vector<pair<int, int>> &a)
{
    int cost = inf;
    for (auto &[x, c] : a)
    {
        vector<int> primes = get_primes(x);
        for (auto &p : primes)
            mp.erase(p);
        primes = get_primes(x + 1);
        for (auto &p : primes)
        {
            if (mp.count(p))
                cost = min(cost, c);
        }
        primes = get_primes(x);
        for (auto &p : primes)
            mp[p]++;
    }
    return cost;
}

void solve()
{
    int n;
    cin >> n;
    vector<pair<int, int>> a(n);
    for (auto &[f, s] : a)
        cin >> f;
    for (auto &[f, s] : a)
        cin >> s;
    map<int, int> mp;
    if (check(mp, a))
    {
        cout << 0 << endl;
        return;
    }
    int adj_cost = inf;
    sort(all(a), [&](pair<int, int> & a, pair<int, int> & b){
        if(a.second!=b.second)
            return a.second < b.second;
        return a.first < b.first;
    });
    int ans = min(a[0].second+a[1].second,one_check(mp, a));
    vector<int> primes = get_primes(a[0].first);
    for(auto &x: primes)
        mp.erase(x);
    for(auto &[p,c]: mp){
        int need = p - (a[0].first % p);
        ans = min(ans, need * a[0].second);
    }
    cout << ans << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    iota(all(spf), 0);
    for (int i = 2; i < N; i++)
    {
        if (spf[i] == i)
        {
            for (int j = i * i; j < N; j += i)
            {
                spf[j] = min(spf[j], i);
            }
        }
    }
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}