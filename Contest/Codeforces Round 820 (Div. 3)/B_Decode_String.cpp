#include <bits/stdc++.h>
using namespace std;
 void solution(){
    vector<int>v;
    string str;
    int n,x;
    cin>> n;
    char arr[n+2];
    for(int i=0; i<n; i++){
        cin>> arr[i];
    }
    arr[n]= '9',arr[n+1]='9';
    for (int i = 0; i < n; i++)
    {
        if(arr[i+1] == '0'&&arr[i+2] =='0'){
            int a = (int)(arr[i])-48;
            int b = (int)(arr[i+1])-48;
            x = a*10 + b;
            v.push_back(x+96);
            i+=2;
        }
        else if(arr[i+2] == '0'&& arr[i+3] != '0'){
            int a = (int)(arr[i])-48;
            int b = (int)(arr[i+1])-48;
            x = a*10 + b;
            v.push_back(x+96);
            i+=2;
        }else{
            v.push_back(((int)arr[i])+48);
        }
    }
    for (int i = 0; i < v.size(); i++)
    {
        str+=(char)v[i];
    }
    cout<<str<<endl;
}
 int main(){
    int t;
    cin>>t;
    while (t--) solution();
}