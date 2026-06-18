#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl "\n"
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
 int main()
{
    fastIO;
    int n, m;
    string str;
    cin >> n >> m;
    vector<pair<string, string>> v(n + m);
    for (int i = 0; i < n + m; i++)
    {
        cin >> v[i].first;
        cin >> v[i].second;
        if (i >= n)
            v[i].second.pop_back();
    }
    for (int i = n; i < n + m; i++)
    {
        cout << v[i].first << " " << v[i].second << ";";
        for (int j = 0; j < n; j++)
        {
            if (v[i].second == v[j].second)
            {
                cout << " #" << v[j].first << endl;
                j = n;
            }
        }
    }
}