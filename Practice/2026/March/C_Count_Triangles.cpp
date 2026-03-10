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

const int mt = 0;

struct Lazy_Segment_Tree{
    int n;
    vector<int>lazy,st;

    Lazy_Segment_Tree(int _n){
        n = _n;
        st.resize(4*n);
        lazy.resize(4*n,0);
    }
    
    void propagate(int node, int b, int e){
        if(lazy[node]==mt)
            return;
        st[node]+=((e-b+1)*lazy[node]);
        if(b!=e){
            lazy[2*node] += lazy[node];
            lazy[2*node+1] += lazy[node];
        }
        lazy[node] = 0;
    }
    
    void update(int node, int b, int e, int &l, int &r, int value){
        propagate(node, b, e);
        if(e<l or b>r) return;
        if(b>=l and e<=r){
            lazy[node] = value;
            propagate(node,b,e);
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid,l,r,value);
        update(right, mid+1,e,l,r,value);
        st[node] = st[left]+st[right];
    }
    
    int query(int node, int b, int e, int &l, int &r){
        propagate(node, b, e);
        if(e<l or b>r) return 0;
        if(b>=l and e<=r){
            return st[node];
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        return query(left,b,mid,l,r) + query(right,mid+1,e,l,r);
    }

    void update(int l, int r, int val){
        update(1, 1, n, l, r, val);
    }

    int query(int l, int r){
        return query(1, 1, n, l, r);
    }
};

void solve()
{
    int a, b, c, d;
    cin >> a >> b >> c >> d;
    Lazy_Segment_Tree st(d);
    for(int x = a; x <= b; x++){
        int l = x + b - 1, r = x + c - 1;
        if(l > d){
            st.update(d, d, r - l + 1);
            continue;
        }
        if(r > d){
            st.update(d, d, r - d);
            r = d;
        }
        l = max(l, c);
        if(l <= r and r >= c)
            st.update(l, r, 1);
    }
    int n = d - c + 1;
    vector<int> range(n);
    for(int i = 0; i < n; i++){
        range[i] = st.query(c + i, c + i);
    }
    debug(range)
    for(int i = n - 2; i >= 0; i--){
        range[i] += range[i + 1];
    }
    cout << accumulate(all(range), 0ll) << endl;
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