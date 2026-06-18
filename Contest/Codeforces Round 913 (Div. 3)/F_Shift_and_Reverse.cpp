#include <bits/stdc++.h>
using namespace std;

/********************************Macros********************************/

#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define ff first
#define ss second
#define set_bits(x) __builtin_popcount(x)
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define int long long
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl

/****************************************************************/

typedef long double ld;
typedef unsigned int ui;
typedef unsigned long long ull;
typedef long double lld;
typedef vector<int> vi;
typedef vector<long long> vll;
typedef vector<pair<int,int>> vpi;

/********************************Debugger********************************/

#ifndef ONLINE_JUDGE
#define debug(x) cerr << #x <<": "; _print(x); cerr << endl;
#else
#define debug(x)
#endif

void _print(int t) {cerr << t;}
void _print(string t) {cerr << t;}
void _print(char t) {cerr << t;}
void _print(lld t) {cerr << t;}
void _print(double t) {cerr << t;}
void _print(ull t) {cerr << t;}

template <class T, class V> void _print(pair <T, V> p);
template <class T> void _print(vector <T> v);
template <class T> void _print(set <T> v);
template <class T, class V> void _print(map <T, V> v);
template <class T> void _print(multiset <T> v);
template <class T, class V> void _print(pair <T, V> p) {cerr << "{"; _print(p.ff); cerr << ","; _print(p.ss); cerr << "}";}
template <class T> void _print(vector <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(set <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(multiset <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T, class V> void _print(map <T, V> v) {cerr << "[ "; for (auto i : v) {_print(i); cerr << " ";} cerr << "]";}

/****************************************************************/

bool check(vi &v, int &n){
    int cnt = 0;
    rep(i,0,n){
        if(v[i]>v[(i+1)%n]) cnt++;
    }
    return cnt<=1;
}

void solve()
{
    int n,ans = INT_MIN,cnt = 0;
    cin>>n;
    vi v(n),temp;
    readv(v);
    temp = v;
    reverse(all(temp));
    int y = min_element(all(v)) - v.begin(), z = min_element(all(temp))-temp.begin();
    bool f1 = check(v,n),f2 = check(temp,n);
    if(f1){
        while(cnt<n&&v[y]==v[(y-1+n)%n]){
            y--;
            if(y==-1)   y = n-1;
            cnt++;
        }
    }
    cnt = 0;
    if(f2){
        while(cnt<n&&temp[z]==temp[(z-1+n)%n]){
            z--;
            if(z==-1)   z = n-1;
            cnt++;
        }
    }
    sort(all(temp));
    if(v==temp){
        cout<<0<<endl;
        return;
    }
    if(f1 or f2){
        int ans = INT_MAX;
        if(f1)  ans = min({ans,n-y,2+y});
        if(f2)  ans = min({ans,1+n-z,1+z});
        cout<<ans<<endl;
    }
    else cout<<-1<<endl;
}

int32_t main()
{
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    while (t--)
        solve();
}