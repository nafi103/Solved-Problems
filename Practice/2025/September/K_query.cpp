#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
int tmp;

struct S{
    vector<int> value;

    S(){
        value.clear();
    }

    S(int val){
        value.clear();
        value.push_back(val);
    }

    void read(){
        cin>>tmp;
        value.push_back(tmp);
    }
};

S combine(S &a, S &b){
    S res;
    res.value.reserve(a.value.size() + b.value.size());
    merge(all(a.value), all(b.value), back_inserter(res.value));
    return res;
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(int _n){
        n = _n;
        t.resize(2*n);
    }

    void place(){
        for(int i = n; i<2*n; i++){
            t[i].read();
        }
        build();
    }

    void build(){
        for (int i = n - 1; i > 0; --i) t[i] = combine(t[i<<1], t[i<<1|1]);
    }

    void modify(int p, const S &value) {
        for (t[p += n] = value; p >>= 1; ) t[p] = combine(t[p<<1], t[p<<1|1]);
    }

    int get_greater(S &t, int &k){
        return t.value.end() - upper_bound(all(t.value),k);
    }

    int query(int l, int r, int &k) {
        int res = 0;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l&1) res += get_greater(t[l++],k);
            if (r&1) res += get_greater(t[--r],k);
        }
        return res;
    }
};

void solve()
{
    int n;
    cin>>n;
    Segment_Tree st(n);
    st.place();
    int q;
    cin>>q;
    while(q--){
        int l,r,k;
        cin>>l>>r>>k;
        l--;
        cout<<st.query(l,r,k)<<endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}