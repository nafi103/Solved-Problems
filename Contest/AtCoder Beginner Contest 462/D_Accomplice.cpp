#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace __gnu_pbds;

/*
 * PBDS (Ordered Set)
 * find_by_order(k): Returns iterator to kth element (0-indexed)
 * order_of_key(x): Returns number of elements strictly smaller than x
 */
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
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

template <typename T>
struct Fenwick_Tree{
    int n;
    vector<T> bit;

    Fenwick_Tree(int _n) : n(_n), bit(_n, 0) {}

    T query(int r) const {
        T sum = 0;
        for(; r >= 0; r = (r & (r + 1)) - 1)
            sum += bit[r];
        return sum;
    }

    T query(int l, int r) const {
        if(l > r)
            return 0;
        return query(r) - query(l - 1);
    }

    void add(int idx, T delta){
        for(; idx < n; idx = idx | (idx + 1)){
            bit[idx] += delta;
        }
    }
};

const int N = 1e6;

void solve()
{
    int n, k, ans = 0;
    cin >> n >> k;
    vector<pair<int,int>> arr(n);
    for(auto &[s, t]: arr)
        cin >> s >> t;
    sort(all(arr));

    Fenwick_Tree<int> ft_sum(N + 1), cnt(N + 1);

    for(auto &[s, t]: arr){
        if(s + k > t)
            continue;

        int sum = ft_sum.query(s + k, t);
        int c = cnt.query(s + k, t);
        ans += sum - c * (s + k - 1);

        c = cnt.query(t + 1, N);
        ans += c * (t - (s + k - 1));

        ft_sum.add(t, t);
        cnt.add(t, 1);
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
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}