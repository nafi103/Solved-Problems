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

/****************************************************************/

struct Bucket{
    int capacity, have;
    Bucket(int _capacity, int _have){
        capacity = _capacity;
        have = _have;
    }
    void pour(Bucket &another){
        int can = min(have, another.capacity - another.have);
        have-=can;
        another.have+=can;
    }
};


void solve()
{
    vector<Bucket>buckets;
    for(int i = 0; i<3; i++){
        int c,h;
        cin>>c>>h;
        buckets.pb(Bucket(c,h));
    }
    for(int i = 0,curr = 0, nxt = 1; i<100; i++,curr = (curr+1)%3, nxt = (nxt+1)%3){
        buckets[curr].pour(buckets[nxt]);
    }
    for(int i = 0; i<3; i++){
        cout<<buckets[i].have<<endl;
    }
}

int32_t main()
{
    freopen("mixmilk.in", "r", stdin);
    freopen("mixmilk.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}