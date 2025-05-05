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
    vector<int>cnt;
    int value;

    S(int val = 0){
        cnt.assign(41,0);
        if(val!=0) cnt[val]++;
        value = 0;
    }
};

S combine(S &a, S b){
    S temp(0);
    temp.value = a.value+b.value;
    for(int i = 1; i<=40; i++)
        temp.cnt[i] = a.cnt[i]+b.cnt[i];
    for(int i = 1; i<=40; i++)
        b.cnt[i]+=b.cnt[i-1];
    for(int i = 2; i<=40; i++){
        temp.value+=(a.cnt[i]*b.cnt[i-1]);
    }
    return temp;
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

    void modify(int p, S value) {
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
    int n,q;
    cin>>n>>q;
    vector<int>v(n);
    readv(v);
    Segment_Tree st(n);
    st.place(v);
    while(q--){
        int type;
        cin>>type;
        if(type==1){
            int l,r;
            cin>>l>>r;
            --l;
            cout<<st.query(l,r).value<<endl;
        }else{
            int id,val;
            cin>>id>>val;
            id--;
            st.modify(id,S(val));
        }
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
        // google(z);
        solve();
    }
}