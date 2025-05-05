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

using pii = pair<int,int>;

struct Mole{
    int x,y,hx,hy;
    vector<pii> possible;
    void read(){
        cin>>x>>y>>hx>>hy;
    }
    void write(){
        cout<<x<<" "<<y<<" "<<hx<<" "<<hy<<endl;
    }
    void rotate(){
        possible.pb({x-hx,y-hy});
        possible.pb({-possible.back().ss, possible.back().ff});
        possible.pb({-possible.back().ss, possible.back().ff});
        possible.pb({-possible.back().ss, possible.back().ff});
        for(int i = 0; i<4; i++){
            possible[i].ff+=hx;
            possible[i].ss+=hy;
        }
    }
};

int sq(int n){
    return n*n;
}

bool square(pii a, pii b, pii c, pii d){
    int d1 = sq(a.ff-b.ff)+sq(a.ss-b.ss);
    int d2 = sq(a.ff-c.ff)+sq(a.ss-c.ss);
    int d3 = sq(a.ff-d.ff)+sq(a.ss-d.ss);
    int mx = max({d1,d2,d3});
    if(d1==mx) swap(b,c);
    else if(d3==mx) swap(c,d);
    int AB = sq(a.ff-b.ff)+sq(a.ss-b.ss);
    int BC = sq(b.ff-c.ff)+sq(b.ss-c.ss);
    int CD = sq(c.ff-d.ff)+sq(c.ss-d.ss);
    int AD = sq(a.ff-d.ff)+sq(a.ss-d.ss);
    int AC = sq(a.ff-c.ff)+sq(a.ss-c.ss);
    int BD = sq(b.ff-d.ff)+sq(b.ss-d.ss);
    return (AB and (AB==BC and BC==CD and CD==AD and AC==BD));
}

int check(vector<Mole>moles, int pos){
    int ans = INT_MAX;
    vector<pii> &a = moles[pos].possible, &b = moles[pos+1].possible,
                    &c = moles[pos+2].possible, &d = moles[pos+3].possible;
    for(int i = 0; i<4; i++){
        for(int j = 0; j<4; j++){
            for(int k = 0; k<4; k++){
                for(int l = 0; l<4; l++){
                    if(square(a[i],b[j],c[k],d[l])){
                        ans = min(ans,i+j+k+l);
                    }
                }
            }
        }
    }
    return (ans==INT_MAX? -1: ans);
}

void solve()
{
    int n;
    cin>>n;
    vector<Mole>moles(4*n);
    for(auto &x: moles){
        x.read();
        x.rotate();
    }
    for(int i = 0; i<4*n; i+=4){
        cout<<check(moles,i)<<endl;
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