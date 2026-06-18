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
struct custom_hash {static uint64_t splitmix64(uint64_t x) {x += 0x9e3779b97f4a7c15;x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;x = (x ^ (x >> 27)) * 0x94d049bb133111eb;return x ^ (x >> 31);}
size_t operator()(uint64_t x) const {static const uint64_t FIXED_RANDOM = chrono::steady_clock::now().time_since_epoch().count();return splitmix64(x + FIXED_RANDOM);}};

struct Node
{
    int value;

    Node(int val = inf) : value(val) {}
};

Node combine(Node &a, Node &b)
{
    return Node(min(a.value, b.value));
}

struct Segment_Tree
{
    int n;
    vector<Node> t;

    Segment_Tree(int _n, vector<int> &v)
    {
        n = _n;
        t.resize(2 * n);
        for (int i = n; i < 2 * n; i++)
        {
            t[i] = Node(v[i - n]);
        }
        build();
    }

    void build()
    {
        for (int i = n - 1; i > 0; --i)
            t[i] = combine(t[i << 1], t[i << 1 | 1]);
    }

    void update(int p, int value)
    {
        for (t[p += n] = Node(value); p > 1; p >>= 1)
            t[p >> 1] = combine(t[p], t[p ^ 1]);
    }

    Node query(int l, int r)
    {
        Node res;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1)
        {
            if (l & 1)
                res = combine(res, t[l++]);
            if (r & 1)
                res = combine(t[--r], res);
        }
        return res;
    }
};

void solve()
{
    int n, q;
    cin >> n >> q;
    vector<int> v(n), idx(n);
    for (int i = 0; i < n; i++)
        cin >> v[i];
    unordered_map<int, int, custom_hash> seen_right;
    unordered_map<int, set<int>,custom_hash>mp;
    for (int i = n - 1; i >= 0; i--)
    {
        if (seen_right.count(v[i]) == 0)
        {
            idx[i] = inf;
        }
        else
        {
            idx[i] = seen_right[v[i]];
        }
        seen_right[v[i]] = i;
        mp[v[i]].insert(i);
    }

    vector<array<int, 3>> queries(q);

    for (auto &[t, a, b] : queries)
    {
        cin >> t >> a >> b;
        a--;
    }

    Segment_Tree st(n, idx);
    for (auto &[t, a, b] : queries)
    {
        if (t == 1)
        {
            if (v[a] == b)
                continue;
            int el = v[a], right_id = idx[a];
            auto it = mp[el].lower_bound(a);
            if (it != mp[el].begin())
            {
                auto prev_it = prev(it);
                int id = *prev_it;
                st.update(id, right_id);
            }

            mp[el].erase(a);
            v[a] = b;

            right_id = inf;
            auto new_it = mp[b].upper_bound(a);
            if (new_it != mp[b].end())
            {
                right_id = *new_it;
            }

            idx[a] = right_id;
            mp[b].insert(a);
            st.update(a, right_id);

            el = v[a];
            auto it2 = mp[el].lower_bound(a);
            if (it2 != mp[el].begin())
            {
                auto prev_it = prev(it2);
                int id = *prev_it;
                st.update(id, a);
            }
        }
        else
        {
            int mn = st.query(a, b).value;
            if (mn >= a and mn < b)
            {
                cout << "NO" << endl;
            }
            else
            {
                cout << "YES" << endl;
            }
        }
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}