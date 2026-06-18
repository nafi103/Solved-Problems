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

struct Lazy_Node{
    int value, inc;

    Lazy_Node(){
        value = inc = 0;
    }

    Lazy_Node(int _value, int _inc){
        value = _value;
        inc = _inc;
    }

    void pull(const Lazy_Node &parent){
        if(parent.value){
            inc = parent.inc;
            value = parent.value;
        }else{
            inc += parent.inc;
        }
    }

    bool empty(){
        return value == 0 and inc == 0;
    }

    void clear(){
        value = 0; inc = 0;
    }
};

struct Segment_Tree{
    int n;
    vector<int> st, v;
    vector<Lazy_Node> lazy;

    Segment_Tree(int _n, vector<int>& _v){
        n = _n;
        v = _v;
        st.resize(4 * n);
        lazy.resize(4 * n);
        build(1, 1, n);
    }

    void build(int node, int b, int e){
        if(b == e){
            st[node] = v[b];
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid);
        build(right, mid + 1, e);
        st[node] = st[left] + st[right];
    }

    void propagate(int node, int b, int e){
        if(lazy[node].empty())
            return;
        if(lazy[node].value){
            st[node] = (e - b + 1) * lazy[node].value;
        }
        st[node] += lazy[node].inc * (e - b + 1);
        if(b != e){
            int left = 2 * node, right = 2 * node + 1;
            lazy[left].pull(lazy[node]);
            lazy[right].pull(lazy[node]);
        }
        lazy[node].clear();
    }

    void update(int node, int b, int e, int &l, int &r, const Lazy_Node &upt){
        if(b >= l and e <= r){
            lazy[node].pull(upt);
            propagate(node, b, e);
            return;
        }
        propagate(node, b, e);
        if(b > r or e < l)
            return;
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        update(left, b, mid, l, r, upt);
        update(right, mid + 1, e, l, r, upt);
        st[node] = st[left] + st[right];
    }

    int query(int node, int b, int e, int &l, int &r){
        propagate(node, b, e);
        if(b >= l and e <= r)
            return st[node];
        if(b > r or e < l)
            return 0;
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        return query(left, b, mid, l, r) + query(right, mid + 1, e, l, r);
    }

    void update(int &l, int &r, int value, int inc){
        Lazy_Node upt(value, inc);
        update(1, 1, n, l, r, upt);
    }

    int query(int &l, int &r){
        return query(1, 1, n, l, r);
    }
};

void solve()
{
    int n, q;
    cin >> n >> q;
    vector<int> arr(n + 1);
    for(int i = 1; i <= n; i++)
        cin >> arr[i];
    Segment_Tree st(n, arr);
    while(q--){
        int t;
        cin >> t;
        if(t == 1){
            int a, b, x;
            cin >> a >> b >> x;
            st.update(a, b, 0, x);
        }else if(t == 2){
            int a, b, x;
            cin >> a >> b >> x;
            st.update(a, b, x, 0);
        }else{
            int a, b;
            cin >> a >> b;
            cout << st.query(a, b) << endl;
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