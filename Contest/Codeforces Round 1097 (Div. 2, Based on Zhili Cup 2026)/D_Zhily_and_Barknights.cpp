#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
 using namespace std;
 using namespace chrono;
using namespace __gnu_pbds;
 template <class T>
using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
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
 const int N = 2010;
int fact[N], ifact[N], arr[N], brr[N];
vector<vector<pair<int, int>>> available(N);
 int expo(int a, int b)
{
    int res = 1;
    while (b)
    {
        if (b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}
 int inv(int a)
{
    return expo(a, mod - 2);
}
 struct Fenwick_Tree
{
    int n;
    vector<int> bit;
     Fenwick_Tree(int n)
    {
        this->n = n;
        bit.assign(n + 1, 0);
    }
     void update(int idx, int delta)
    {
        for (; idx <= n; idx += idx & -idx)
            bit[idx] += delta;
    }
     int query(int idx)
    {
        int sum = 0;
        for (; idx > 0; idx -= idx & -idx)
            sum += bit[idx];
        return sum;
    }
     int query(int l, int r)
    {
        if (l > r)
            return 0;
        return query(r) - query(l - 1);
    }
};
 void solve()
{
    int n;
    cin >> n;
     for (int i = 0; i < n; i++)
    {
        available[i].clear();
        cin >> arr[i];
    }
    for (int i = 0; i < n; i++)
    {
        cin >> brr[i];
    }
     if (n == 1)
    {
        cout << 0 << endl;
        return;
    }
     vector<int> s;
    s.reserve(n * n);
    for (int i = 0; i < n; i++)
    {
        for (int j = 0; j < n; j++)
        {
            s.push_back(arr[i] * brr[j]);
        }
    }
    sort(s.begin(), s.end());
    s.erase(unique(s.begin(), s.end()), s.end());
     for (int i = 0; i < n; i++)
    {
        vector<int> temp_ids;
        temp_ids.reserve(n);
         for (int j = 0; j < n; j++)
        {
            int val = arr[i] * brr[j];
            int id = lower_bound(s.begin(), s.end(), val) - s.begin() + 1;
            temp_ids.push_back(id);
        }
         sort(temp_ids.begin(), temp_ids.end());
         for (int id : temp_ids)
        {
            if (available[i].empty() || available[i].back().first != id)
            {
                available[i].push_back({id, 1});
            }
            else
            {
                available[i].back().second++;
            }
        }
    }
     int id = sz(s);
    Fenwick_Tree st(id);
    pbds<pair<int, int>> anum;
    for (int i = 0; i < n; i++)
    {
        for (auto &[f, s] : available[i])
        {
            st.update(f, s);
        }
        anum.insert({arr[i], i});
    }
     int numerator = 0;
    for (int i = 0; i < n; i++)
    {
        for (auto &[f, s] : available[i])
        {
            st.update(f, -s);
        }
        anum.erase({arr[i], i});
        int less_ai = anum.order_of_key({arr[i], -inf});
        for (auto &[c, s] : available[i])
        {
            int valid_pair = st.query(1, c - 1) - less_ai;
            numerator = (numerator + (valid_pair * fact[n - 2]) % mod * s) % mod;
        }
    }
    cout << (numerator * ifact[n]) % mod << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
     fact[0] = 1;
    for (int i = 1; i < N; i++)
    {
        fact[i] = (fact[i - 1] * i) % mod;
    }
    ifact[N - 1] = inv(fact[N - 1]);
    for (int i = N - 2; i >= 0; i--)
    {
        ifact[i] = (ifact[i + 1] * (i + 1)) % mod;
    }
     int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}