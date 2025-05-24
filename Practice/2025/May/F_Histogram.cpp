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
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

struct S{
    int value;

    S(int val = inf) : value(val) {}

    void read(){
        cin>>value;
    }
};

S combine(S &a, S &b){
    return S(min(a.value,b.value));
}

struct Segment_Tree{
    int n;
    vector<S>t;

    Segment_Tree(int _n){
        n = _n;
        t.resize(2*n);
    }

    void place(vector<int>&v){
        for(int i = n; i<2*n; i++){
            t[i] = S(v[i-n]);
        }
        build();
    }

    void build(){
        for (int i = n - 1; i > 0; --i) t[i] = combine(t[i<<1], t[i<<1|1]);
    }

    void modify(int p, const S &value) {
        for (t[p += n] = value; p >>= 1; ) t[p] = combine(t[p<<1], t[p<<1|1]);
    }

    S query(int l, int r) {
        S resl, resr;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
            if (l&1) resl = combine(resl, t[l++]);
            if (r&1) resr = combine(t[--r], resr);
        }
        return combine(resl, resr);
    }
};


void solve()
{
    int n;
    cin>>n;
    Segment_Tree st(n);
    vector<int>v(n);
    readv(v);
    st.place(v);
    int ans = n;
    for(int i = 0; i<n; i++){
        int left = i, right = i;
        if(i){
            int l = 0, r = left;
            while(l<=r){
                int mid = (l+r)/2;
                if(st.query(mid,i+1).value>=v[i]){
                    r = mid-1;
                }else{
                    l = mid+1;
                }
            }
            left = l;
        }
        if(i<n-1){
            int l = i, r = n-1;
            while(l<=r){
                int mid = (l+r)/2;
                if(st.query(i,mid+1).value>=v[i]){
                    l = mid+1;
                }else{
                    r = mid-1;
                }
            }
            right = r;
        }
        ans = max(ans,(right-left+1)*v[i]);
    }
    cout<<ans<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}