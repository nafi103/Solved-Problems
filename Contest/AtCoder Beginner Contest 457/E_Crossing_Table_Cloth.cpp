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

/*
 * Standard Segment Tree (Point Update, Range Query)
 * Time: O(N) build, O(log N) update/query
 * Use: Range Sum, Range Min/Max, Range GCD
 */

struct Segment_Tree {

    struct Node {
        int value;
        Node(int val = inf) : value(val) {} 
        // Default values: sum -> 0, min -> inf, max -> -inf
    };

    Node merge(const Node &left, const Node &right) {
        return Node(min(left.value,right.value));
    }

    int n;
    vector<Node> st;

    Segment_Tree(const vector<int> &v, int _n) {
        n = _n;
        st.resize(4 * n + 1);
        build(1, 1, n, v);
    }

    void build(int node, int b, int e, const vector<int> &v) {
        if (b == e) {
            st[node] = Node(v[b]);
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid, v);
        build(right, mid + 1, e, v);
        st[node] = merge(st[left], st[right]);
    }

    Node query(int node, int b, int e, int l, int r) {
        if (e < l or b > r) return Node();
        if (b >= l and e <= r) return st[node];
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        Node query_left = query(left, b, mid, l, r);
        Node query_right = query(right, mid + 1, e, l, r);
        return merge(query_left, query_right);
    }

    int query(int l, int r){
        if(l > r)
            return inf;
        return query(1, 1, n, l, r).value;
    }
};

void solve()
{
    int n, m;
    cin >> n >> m;

    map<pair<int,int>, int> cnt;
    vector<vector<int>> pref(n + 1), suff(n + 1);
    vector<int> arr(n + 1, inf);

    for(int i = 0, l, r; i < m; i++){
        cin >> l >> r;
        pref[l].push_back(r);
        suff[r].push_back(l);
        cnt[{l, r}]++;
        arr[l] = min(arr[l], r);
    }

    Segment_Tree st(arr, n);

    for(int i = 1; i <= n; i++){
        if(!pref[i].empty())
            sort(all(pref[i]));
        if(!suff[i].empty())
            sort(all(suff[i]));
    }

    int q;
    cin >> q;
    while(q--){
        int l, r;
        cin >> l >> r;
        int lmax = -inf, rmin = inf;
        if(!pref[l].empty()){
            auto it = upper_bound(all(pref[l]), r);
            if(it != pref[l].begin()){
                it--;
                if(*it <= r and *it >= l)
                    lmax = *it;
            }
        }

        if(!suff[r].empty()){
            auto it = upper_bound(all(suff[r]), l - 1);
            if(it != suff[r].end() and *it <= r)
                rmin = *it;
        }

        if(lmax != -inf and rmin != inf){
            if(rmin - lmax > 1){
                cout << "No" << endl;
            }else{
                if(lmax == r and rmin == l){ // one segment covering
                    if(cnt[{l, r}] > 1 or st.query(l + 1, r) <= r or st.query(l, l) < r){
                        cout << "Yes" << endl;
                    }else{
                        cout << "No" << endl;
                    }
                }else{
                    cout << "Yes" << endl;
                }
            }
        }else{
            cout << "No" << endl;
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